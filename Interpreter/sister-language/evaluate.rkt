#lang racket

(require rackunit)
(require "logging.rkt")
(require "../utils.rkt")
(require "ast.rkt")
(require "parse.rkt")
(require "typecheck.rkt")

(provide (all-defined-out))

;;values: FixClos?, Clos?, Prim?, Const?, box?, Quote?
(struct FixClos (rec-param ;; symbol
                 param ;; symbol
                 body  ;; meta term/object term
                 env   ;; dict from symbol to values
                 ) #:transparent #:mutable)
(struct Clos (param ;; symbol
              body  ;; meta term/object term
              env   ;; dict from symbol to values
              ) #:transparent #:mutable)
(struct ECClos (ec-param
                ec-lower
                ec-bound
                body  ;; meta term/object term
                env   ;; dict from symbol to values
                ) #:transparent)
(struct ECVal (name) #:transparent)
(struct Prim (n-args ;; No. of arguments
              fun    ;; Curried racket procedure accepting "n-args" number of
                     ;; values and returning a value
              ) #:transparent)

(define (value? v)
  (match v
    [(Const _) #t]
    [(Prim (? natural?) (? procedure?)) #t]
    [(? box? b) (value? (unbox b))]
    [(Quote Mᵒ (ECVal 'ε))
     (unless (stlc-term? Mᵒ)
       (log debug "Quoted ~a not a value because it is not a valid object term." Mᵒ)
       #f)
     #t]
    [(FixClos (? id? f) (? id? x) body (? dict? env))
     #t]
    [(Clos (? id? x) body (? dict? env))
     #t]
    [(ECClos (? id? α) (ECVal δ) (ECVal γ) body (? dict? env))
     #:when (and (or (id? δ) (equal? δ #f))
                 (or (id? γ) (equal? γ #f)))
     #t]
    [_
     (log debug "Invalid value:~a" v)
     #f]))

(define (lift-prim-1 p)
  (λ (y)
    (match-let ([(Const n) y])
      (Const (p n)))))

(define (lift-prim-2 p)
  (λ (x)
    (λ (y)
      (match-let ([(Const m) x]
                  [(Const n) y])
        (Const (p m n))))))

(define primitives
  (hasheqv
   'zero? (Prim 1 (lift-prim-1 zero?))
   'sub1 (Prim 1 (lift-prim-1 sub1))
   '+ (Prim 2 (lift-prim-2 +))
   '- (Prim 2 (lift-prim-2 -))
   '* (Prim 2 (lift-prim-2 *))
   '/ (Prim 2 (lift-prim-2 quotient))
   '% (Prim 2 (lift-prim-2 remainder))))

(define empty-env
  (hash))

(define (eval-ec ec env)
  (match ec
    [(ECEps) (ECEps)]
    [(ECVar α) (ECVal (dict-ref env α))]))

;; precondition: (meta-typecheck term)
(define (meta-evaluate term [env empty-env])
  (meta-evaluate^ meta-evaluate eval-quoted-obj term env))

(define (meta-evaluate^ self quote-eval term env)
  (define (recurse term^) (self term^ env))
  (match term
    [(MVar x) (dict-ref env x)]
    [(MFixAbs f x A B M) (FixClos f x M env)]
    [(MAbs x A M) (Clos x M env)]
    [(ECAbs α lb ub M)
     (define lb-val (if lb (eval-ec lb env) #f))
     (define ub-val (if ub (eval-ec ub env) #f))
     (ECClos α lb-val ub-val M env)]
    [(ECApp M ec)
     (match-define (ECClos α lb ub N env^) (recurse M))
     (self N (dict-set env^ α (eval-ec ec env)))]
    [(Ref M) (box (recurse M))]
    [(Set M N)
     (set-box! (recurse M) (recurse N))
     (Const '())]
    [(Deref M) (unbox (recurse M))]
    [(Quote Mᵒ ec)
     (Quote (quote-eval Mᵒ env) (eval-ec ec env))]
    [_ (*-evaluate self term env)]))

;; precondition: (object-typecheck term)
(define (eval-quoted-obj term env)
  (eval-quoted-obj^ eval-quoted-obj meta-evaluate term env))

(define (eval-quoted-obj^ self meta-eval term env)
  (define (recurse term^) (self term^ env))
  (match term
    [(or (OVar _) (Const _)) term]
    [(OFixAbs α f x T S Mᵒ)
     (define dyn-α (gen-id α))
     (OFixAbs dyn-α f x T S (self Mᵒ (dict-set env α (ECVal dyn-α))))]
    [(OAbs α x T Mᵒ)
     (define dyn-α (gen-id α))
     (OAbs dyn-α x T (self Mᵒ (dict-set env α (ECVal dyn-α))))]
    [(App Lᵒ Mᵒ)
     (App (recurse Lᵒ) (recurse Mᵒ))]
    [(If Lᵒ Mᵒ Nᵒ)
     (If (recurse Lᵒ) (recurse Mᵒ) (recurse Nᵒ))]
    [(Splice M)
     (define evald-M (meta-eval M env))
     (match evald-M
       [(Quote Mᵒ _) Mᵒ]
       [_ (error 'eval-quoted-object
                 "in splice, expected quoted code, not ~a"
                 evald-M)])]
    [(Asc Mᵒ _) (recurse Mᵒ)]
    ))

;; precondition: (object-typecheck term)
(define (object-evaluate term [env (hash)])
  (object-evaluate^ object-evaluate term env))

(define (object-evaluate^ self term env)
  (match term
    [(OVar x) (dict-ref env x)]
    [(OFixAbs α f x A B M) (FixClos f x M env)]
    [(OAbs α x A M) (Clos x M env)]
    [_ (*-evaluate self term env)]))

(define (*-evaluate self term [env (hash)])
  (define (recurse term^) (self term^ env))
  (match term
    [(Const k)
     (cond
       [(dict-has-key? primitives k)
        (dict-ref primitives k)]
       [else (Const k)])]
    [(App M N)
     (define evald-M (recurse M))
     (define evald-N (recurse N))
     (apply-fun self evald-M evald-N)]
    [(If L M N)
     (define b (Const-name (recurse L)))
     (cond
       [b (recurse M)]
       [else (recurse N)])]))

(define (apply-fun interp fun arg)
  (match fun
    [(FixClos f x M env^) (interp M (dict-set (dict-set env^ x arg)
                                              f (FixClos f x M env^)))]
    [(Clos x M env^) (interp M (dict-set env^ x arg))]
    [(Prim 1 f) (f arg)]
    [(Prim n f) #:when (> n 1) (Prim (sub1 n) (f arg))]))

(define (full-evaluate term)
  (meta-typecheck term)
  (define evald-term (meta-evaluate term))
  (match evald-term
    [(Quote Mᵒ _) (object-evaluate Mᵒ)]
    [_ evald-term]))

(define-check (check-full-eval-equiv? term expected-val)
  (define evald-term (full-evaluate term))
  (unless (and (value? evald-term)
               (object-term-α-equiv? evald-term expected-val))
    (fail-check
     (format
      (string-append "The input term:~n~v~nevaluated to:~n~v~nwhich is "
                     "either not a value or not equal to the expected value:~n~v~n")
      (unparse-meta-term term)
      evald-term
      expected-val))))
