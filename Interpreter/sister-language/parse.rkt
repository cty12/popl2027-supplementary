#lang racket

(require "ast.rkt")
(require "tools.rkt")
(require "../utils.rkt")

(provide (all-defined-out))

(struct ParseException (term reason))

(define (parse-meta-type t)
  (with-handlers
    ([ParseException?
      (λ (e)
        (error 'parse-meta-type
               "Failed to parse meta-type:~n~v~nReason: ~a"
               (ParseException-term e)
               (ParseException-reason e)))])
    (match t
      [`(Ref ,a) (RefT (parse-meta-type a))]
      [`(‶ ,ot ″ ,ec)
       (define αv (parse-ec ec))
       (Code (parse-object-type ot) αv)]
      [`(∀̇ (,γ <: ,α <: ,β) ,body)
       (define lb (parse-ec-opt γ))
       (define ub (parse-ec-opt β))
       (ECUniv α lb ub (parse-meta-type body))]
      [_ (parse-*-type parse-meta-type t)])))

(define (parse-ec e)
  (match e
    ['ε (ECEps)]
    [α #:when (symbol? α)
       (ECVar α)]
    [else
     (error 'parse-ec
            "Failed to parse environment classifier:~n~v"
            e)]))

(define (parse-ec-opt e)
  (match e
    ['_ #f]
    [else (parse-ec e)]))

(define (parse-object-type t)
  (with-handlers
      ([ParseException?
        (λ (e)
          (error 'parse-object-type
                 "Failed to parse object-type ~a because ~a"
                 (ParseException-term e)
                 (ParseException-reason e)))])
    (parse-*-type parse-object-type t)))

(define (parse-*-type self t)
  (match t
    [b #:when (symbol? b) (Base b)]
    [`(→ ,t1 ,t2) (Fun (self t1) (self t2))]
    [_ (raise (ParseException t "invalid type"))]))

(define (parse-meta-term e)
  (with-handlers
      ([ParseException?
        (λ (e)
          (error 'parse-meta-term
                 "Failed to parse meta-term:\n\"~v\"\nReason: ~a"
                 (ParseException-term e)
                 (ParseException-reason e)))])
    (match e
      [x
       #:when (symbol? x)
       (MVar x)]
      [`(fixλ ,f (,x : ,A) : ,B ,body)
       #:when (and (symbol? x) (symbol? f))
       (MFixAbs f x (parse-meta-type A) (parse-meta-type B)
                (parse-meta-term body))]
      [`(λ (,x : ,A) ,body)
       #:when (symbol? x)
       (MAbs x (parse-meta-type A) (parse-meta-term body))]
      [`(let* ,bindings ,body)
       (define rev-bindings^
         (for/fold ([bindings^ '()])
                   ([binding bindings])
           (match binding
             [`((,x : ,A) ,rhs)
              #:when (symbol? x)
              `((,x
                 ,(parse-meta-type A)
                 ,(parse-meta-term rhs))
                .
                ,bindings^)]
             [_ (raise (ParseException binding "invalid binding syntax in let*"))])))
       (for/fold ([result (parse-meta-term body)])
                 ([binding rev-bindings^])
         (match-let ([`(,x ,T ,rhs) binding])
           (App (MAbs x T result) rhs)))]
      [`(Λ (,δ <: ,α <: ,β) ,body)
       #:when (and (symbol? δ) (symbol? α) (symbol? β))
       (define lb (parse-ec-opt δ))
       (define ub (parse-ec-opt β))
       (ECAbs α lb ub
              (parse-meta-term body))]
      [`(,f [,α])
       (define ec (parse-ec α))
       (ECApp (parse-meta-term f) ec)]
      [`(ref ,m)
       (Ref (parse-meta-term m))]
      [`(,m := ,n)
       (Set (parse-meta-term m) (parse-meta-term n))]
      [`(! ,m)
       (Deref (parse-meta-term m))]
      [`(‶ ,mᵒ ″ ,α)
       (define ec (parse-ec α))
       (Quote (parse-object-term mᵒ) ec)]
      [`(begin ,@assigns ,return)
       (define assigns^
         (for/list ([a assigns])
           (match a
             [`(,lhs := ,rhs) (parse-meta-term a)]
             [_
              (raise (ParseException
                      a
                      (string-append "only assignment expressions allowed in "
                                     "the non-final subexpressions of begin")))])))
       (for/foldr ([result (parse-meta-term return)])
         ([a assigns^])
         (App (MAbs (gensym '_) (Base 'Unit)  result) a))]
      [_ (parse-*-term parse-meta-term e)])))

(define (parse-object-term e)
  (with-handlers
    ([ParseException?
        (λ (e)
          (error 'parse-object-term
                 "Failed to parse object-term \"~a\" because ~a"
                 (ParseException-term e)
                 (ParseException-reason e)))])
    (match e
      [x
       #:when (symbol? x)
       (OVar x)]
      [`(λ ,α (,x : ,T) ,body)
       #:when (and (symbol? α) (symbol? x))
       (OAbs α x (parse-object-type T)
             (parse-object-term body))]
      [`(fixλ ,α ,f (,x : ,T) : ,S ,body)
       #:when (and (symbol? α) (symbol? f) (symbol? x))
       (OFixAbs α f x (parse-object-type T) (parse-object-type S)
                (parse-object-term body))]
      [`(~ ,m)
       (Splice (parse-meta-term m))]
      [`(,Mᵒ :: ,T)
       (Asc (parse-object-term Mᵒ)
            (parse-object-type T))]
      [`(let* ,bindings ,body)
       (define rev-bindings^
         (for/fold ([bindings^ '()])
                   ([binding bindings])
           (match binding
             [`((,x : ,α ,T) ,rhs)
              #:when (and (symbol? α) (symbol? x))
              `((,x
                 ,α
                 ,(parse-object-type T)
                 ,(parse-object-term rhs))
                .
                ,bindings^)]
             [_ (error 'parse-object-term
                       "Invalid binding syntax in let*: ~a"
                       binding)])))
       (for/fold ([result (parse-object-term body)])
                 ([binding rev-bindings^])
         (match-let ([`(,x ,α ,T ,rhs) binding])
           (App (OAbs α x T result) rhs)))]
      [_ (parse-*-term parse-object-term e)])))

(define (parse-*-term self e)
  (match e
    [c #:when (not (or (symbol? c) (pair? c))) (Const c)]
    [`',c (Const c)]
    [`(,m ,n) (App (self m) (self n))]
    [`(if ,test ,then ,else) (If (self test) (self then) (self else))]
    [_ (raise (ParseException e (format "invalid term:\n~a" e)))]))

(define (unparse-meta-type type)
  (match type
    [(RefT A) `(Ref ,(unparse-meta-type A))]
    [(Code T ec) `(‶ ,(unparse-object-type T) ″ ,(unparse-ec ec))]
    [(ECUniv α lb ub A)
     (define γ (if (not lb) '_ (unparse-ec lb)))
     (define β (if (not ub) '_ (unparse-ec ub)))
    `(∀̇ (,γ <: ,α <: ,β) ,(unparse-meta-type A))]
    [_ (unparse-*-type unparse-meta-type type)]))

(define (unparse-ec ec)
  (match ec
    [(ECEps) 'ε]
    [(ECVar α) (id->symbol α)]
    [else
     (error 'unparse-ec "unrecognized EC: ~a" ec)]))

(define (unparse-object-type type)
  (unparse-*-type unparse-object-type type))

(define (unparse-*-type self type)
  (match type
    [(Base b) b]
    [(Fun T1 T2) `(→ ,(self T1) ,(self T2))]
    [_ (error 'unparse-*-type "Invalid AST ~a" type)]))

(define (unparse-meta-term term)
  (match term
    [(MAbs x A body)
     `(λ (,(id->symbol x) : ,(unparse-meta-type A)) ,(unparse-meta-term body))]
    [(MFixAbs f x A B body)
     `(fixλ ,(id->symbol f) (,(id->symbol x) : ,(unparse-meta-type A)) : ,B ,(unparse-meta-term body))]
    [(MVar x) (id->symbol x)]
    [(ECAbs α lb ub body)
     (define γ^ (if (not lb) '_ (unparse-ec lb)))
     (define β^ (if (not ub) '_ (unparse-ec ub)))
     `(Λ (,γ^ <: ,α <: ,β^) ,(unparse-meta-term body))]
    [(ECApp M ec) `(,(unparse-meta-term M) [,(unparse-ec ec)])]
    [(Ref M) `(ref ,(unparse-meta-term M))]
    [(Set M N) `(,(unparse-meta-term M) := ,(unparse-meta-term N))]
    [(Deref M) `(! ,(unparse-meta-term M))]
    [(Quote Mᵒ ec) `(‶ ,(unparse-object-term Mᵒ) ″ ,(unparse-ec ec))]
    [_ (unparse-*-term unparse-meta-term term)]))

(define (unparse-object-term term)
  (match term
    [(OVar x) x]
    [(OAbs α x T body)
     `(λ ,(id->symbol α) (,(id->symbol x) : ,(unparse-object-type T)) ,(unparse-object-term body))]
    [(OFixAbs α f x T S body)
     `(fixλ ,(id->symbol α) ,(id->symbol f) (,(id->symbol x) : ,(unparse-object-type T)) : ,(unparse-object-type T)
            ,(unparse-object-term body))]
    [(Splice M) `(~ ,(unparse-meta-term M))]
    [(Asc Mᵒ T) `(,(unparse-object-term Mᵒ) :: ,(unparse-object-type T))]
    [_ (unparse-*-term unparse-object-term term)]))

(define (unparse-*-term self term)
  (match term
    [(Const k)
     (cond
       [(or (symbol? k) (pair? k)) `',k]
       [else k])]
    [(App M N) `(,(self M) ,(self N))]
    [(If L M N) `(if ,(self L) ,(self M) ,(self N))]
    [_ (error 'unparse-*-term "Invalid term: ~a" term)]))

(define read-term
  (read-program
   (λ (p)
     (parse-meta-term (caddr p)))))
(define read-type
  (read-program
   (λ (p)
     (parse-meta-type (caddr p)))))

;(require racket/trace)
;(trace parse-meta-term)
;(trace parse-meta-type)
