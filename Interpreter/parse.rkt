#lang racket

(require racket/syntax-srcloc)
(require syntax/parse)
(require "ast.rkt")
(require "utils.rkt")
(require "sister-language/tools.rkt")

(provide (all-defined-out))

(struct ParseException (term reason))

(define (parse-ec e)
  (syntax-parse e
    #:datum-literals (⋆ ε)
    [⋆ (Dyn)]
    [ε (ECEps)]
    [α:id (ECVar (syntax-e #'α))]
    [_
     (error 'parse-ec
            "Failed to parse environment classifier:~n~v"
            (syntax-e #'e))]))

(define (parse-ec-opt e)
  (syntax-parse e
    #:datum-literals (_)
    [_ #f]
    [e (parse-ec #'e)]))

(define (check-ec-param param-stx stx)
  (define α (syntax-e param-stx))
  (when (or (eqv? α '⋆) (eqv? α 'ε))
    (error 'invalid-ec-param
            "In :~n~v~nEnvironment classifier ~a parameter cannot be ⋆ or ε"
            (syntax->datum stx) α)))

(define (parse-meta-type t)
  (with-handlers
    ([ParseException?
      (λ (e)
        (error 'parse-meta-type
               "Failed to parse meta-type:~n~v~nReason: ~a"
               (ParseException-term e)
               (ParseException-reason e)))])
    (syntax-parse t
      #:datum-literals (⋆ ‶ ″ Ref ∀̇ <:)
      [⋆ (Dyn)]
      [(‶ C ″ α:id)
       (define ec (parse-ec #'α))
       (Code (parse-gradual-object-type #'C) ec)]
      [(Ref a) (RefT (parse-meta-type #'a))]
      [(∀̇ (γ:id <: α:id <: β:id) body)
       (check-ec-param #'α t)
       (define lb (parse-ec-opt #'γ))
       (define ub (parse-ec-opt #'β))
       (ECUniv (syntax-e #'α) lb ub
               (parse-meta-type #'body))]
      [_ (parse-*-type parse-meta-type t)])))

(define (parse-gradual-object-type t)
  (with-handlers
    ([ParseException?
      (λ (e)
        (error 'parse-gradual-object-type
               "Failed to parse object-type:~n~v~nReason: ~a"
               (ParseException-term e)
               (ParseException-reason e)))])
    (syntax-parse t
      #:datum-literals (⋆)
      [⋆ (Dyn)]
      [_ (parse-*-type parse-gradual-object-type t)])))

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
  (syntax-parse t
    #:datum-literals (→)
    [b:id  (Base (syntax-e #'b))]
    [(→ t1 t2) (Fun (self #'t1) (self #'t2))]
    [_ (raise (ParseException t "invalid type"))]))

(define (parse-meta-term e)
  (define ℓ (Label (syntax-srcloc e)))
  (syntax-parse e
    #:datum-literals (λ : fixλ let* Λ <: ref := ! ‶ ″ begin if quote blame)
    [(λ (x:id : A) body)
     (MAbs (syntax-e #'x) (parse-meta-type #'A) (parse-meta-term #'body))]
    [(λ (x:id) body)
     (MAbs (syntax-e #'x) (Dyn) (parse-meta-term #'body))]
    [(fixλ f:id (x:id : A) : B body)
     (MFixAbsℓ (syntax-e #'f) (syntax-e #'x) (parse-meta-type #'A) (parse-meta-type #'B)
               (parse-meta-term #'body) ℓ)]
    [(let* (bindings ...) body)
     (LetStar (map parse-meta-binding (syntax-e #'(bindings ...))) (parse-meta-term #'body))]
    [x:id
     (MVar (syntax-e #'x))]
    [(Λ (δ:id <: α:id <: β:id) body)
     (check-ec-param #'α e)
     (define lb (parse-ec-opt #'δ))
     (define ub (parse-ec-opt #'β))
     (ECAbs (syntax-e #'α) lb ub (parse-meta-term #'body))]
    [(f [α:id])
     (define ec (parse-ec #'α))
     (ECAppℓ (parse-meta-term #'f) ec ℓ)]
    [(ref m)
     (Ref (parse-meta-term #'m))]
    [(m := n)
     (Setℓ (parse-meta-term #'m) (parse-meta-term #'n) ℓ)]
    [(! m)
     (Derefℓ (parse-meta-term #'m) ℓ)]
    [(‶ mᵒ ″ α:id)
     (define ec (parse-ec #'α))
     (Quote (parse-object-term #'mᵒ) ec)]
    [(begin assigns ... return)
     (Begin (map parse-meta-term (syntax-e #'(assigns ...)))
            (parse-meta-term #'return))]
    [(if test then else)
     (Ifℓ (parse-meta-term #'test) (parse-meta-term #'then) (parse-meta-term #'else) ℓ)]
    [c #:when (not (or (symbol? (syntax-e #'c)) (pair? (syntax-e #'c)))) (Const (syntax-e #'c))]
    ['c (Const (syntax-e #'c))]
    [(blame A ℓ:string)
     ;; need this for checking result of test examples
     (match-define (list source line) (string-split (syntax-e #'ℓ) ":"))
     (Blame (parse-meta-type #'A)
            (Label (srcloc source (string->number line) #f #f #f)))]
    [(m n)
     (Appℓ (parse-meta-term #'m) (parse-meta-term #'n) ℓ)]
    [_ (error 'parse-meta-term "invalid term:\n~a" e)]))

(define (parse-meta-binding binding)
  (syntax-parse binding
    #:datum-literals (:)
    [(var:id rhs)
     (LetBind (syntax-e #'var) (parse-meta-term #'rhs))]
    [((var:id : type) rhs)
     (define ℓ (Label (syntax-srcloc binding)))
     (LetBindTypeℓ (syntax-e #'var) (parse-meta-type #'type) (parse-meta-term #'rhs) ℓ)]
    [_ (error 'parse-meta-binding "Invalid meta binding:~a" binding)]))

(define (parse-object-term e)
  (syntax-parse e
    #:datum-literals (λ fixλ ~ :: let* : if quote)
    [x:id
     (OVar (syntax-e #'x))]
    [(λ (x:id : T) body)
     (OAbs (gen-id '_) (syntax-e #'x) (parse-object-type #'T) (parse-object-term #'body))]
    [(λ α:id (x:id : T) body)
     (check-ec-param #'α e)
     (OAbs (syntax-e #'α) (syntax-e #'x) (parse-object-type #'T) (parse-object-term #'body))]
    [(fixλ f:id (x:id : T) : S body)
     (OFixAbs (gen-id '_) (syntax-e #'f) (gen-id '_) (syntax-e #'x)
              (parse-object-type #'T) (parse-object-type #'S)
              (parse-object-term #'body))]
    [(fixλ α:id f:id (x:id : T) : S body)
     (check-ec-param #'α e)
     (OFixAbs (syntax-e #'α) (syntax-e #'f) (gen-id '_) (syntax-e #'x)
              (parse-object-type #'T) (parse-object-type #'S)
              (parse-object-term #'body))]
    [(fixλ α:id f:id β:id (x:id : T) : S body)
     (check-ec-param #'α e)
     (check-ec-param #'β e)
     (OFixAbs (syntax-e #'α) (syntax-e #'f) (syntax-e #'β) (syntax-e #'x)
              (parse-object-type #'T) (parse-object-type #'S)
              (parse-object-term #'body))]
    [(~ m)
     (Spliceℓ (parse-meta-term #'m) (Label (syntax-srcloc e)))]
    [(Mᵒ :: T)
     (Asc (parse-object-term #'Mᵒ)
          (parse-gradual-object-type #'T))]
    [(let* (bindings ...) body)
     (LetStar (map parse-object-binding (syntax-e #'(bindings ...)))
              (parse-object-term #'body))]
    [(if test then else)
     (If (parse-object-term #'test) (parse-object-term #'then) (parse-object-term #'else))]
    [c #:when (not (or (symbol? (syntax-e #'c)) (pair? (syntax-e #'c)))) (Const (syntax-e #'c))]
    ['c (Const (syntax-e #'c))]
    [(m n)
     (App (parse-object-term #'m) (parse-object-term #'n))]
    [_ (error 'parse-object-term "invalid term:\n~a" e)]))

(define (parse-object-binding binding)
  (syntax-parse binding
    #:datum-literals (:)
    [(x:id rhs)
     (LetBind (syntax-e #'x) (parse-object-term #'rhs))]
    [((x:id α:id) rhs)
     (check-ec-param #'α binding)
     (LetBindα (syntax-e #'x) (syntax-e #'α) (parse-object-term #'rhs))]
    [((x:id : T) rhs)
     (LetBindType (syntax-e #'x) (parse-object-type #'T) (parse-object-term #'rhs))]
    [((x:id : α:id T) rhs)
     (check-ec-param #'α binding)
     (LetBindαType (syntax-e #'x) (syntax-e #'α) (parse-object-type #'T) (parse-object-term #'rhs))]
    [_ (error 'parse-object-binding "Invalid object binding:~a" binding)]))

(define (unparse-object-type type)
  (match type
    [(Dyn) '⋆]
    [_ (unparse-*-type unparse-object-type type)]))

(define (unparse-ec ec)
  (match ec
    [(Dyn) '⋆]
    [(ECEps) 'ε]
    [(ECVar α) (id->symbol α)]
    [else
     (error 'unparse-ec "unrecognized EC: ~a" ec)]))

(define (unparse-meta-type type)
  (match type
    [(Dyn) '⋆]
    [(Code T ec) `(‶ ,(unparse-object-type T) ″ ,(unparse-ec ec))]
    [(RefT A) `(Ref ,(unparse-meta-type A))]
    [(ECUniv α lb ub A)
     (define γ (if (not lb) '_ (unparse-ec lb)))
     (define β (if (not ub) '_ (unparse-ec ub)))
    `(∀̇ (,γ <: ,α <: ,β) ,(unparse-meta-type A))]
    [(ECUnivCC α A)
     `(∀̇ ,α ,(unparse-meta-type A))]
    [(ECSub sub-ec sup-ec A)
     (define γ (unparse-ec sub-ec))
     (define β (unparse-ec sup-ec))
    `(,γ <: ,β ⇒ ,(unparse-meta-type A))]
    [_ (unparse-*-type unparse-meta-type type)]))

(define (unparse-*-type self type)
  (match type
    [(Base b) b]
    [(Fun T1 T2) `(→ ,(self T1) ,(self T2))]
    [_ (error 'unparse-*-type "Invalid AST ~a" type)]))

(define (unparse-label ℓ)
  (match-define (Label (srcloc source line _ _ _)) ℓ)
  (format "~a:~a" source line))

;; By default, the S-expression unparser omits the per-node `@ label` suffix
;; because that would clutter a type error. (Basically in a type error I want to
;; look at just the surface term without a blame label attached to each AST.)
(define print-labels? (make-parameter #f))

(define (label-suffix ℓ)
  (if (print-labels?) `(@ ,(unparse-label ℓ)) '()))

;; The source label carried by a labeled term node (meta or object). Returns #f
;; for nodes that carry no label.
(define (term-label t)
  (match t
    [(LetBindTypeℓ _ _ _ ℓ) ℓ]
    [(Spliceℓ _ ℓ) ℓ]
    [(MFixAbsℓ _ _ _ _ _ ℓ) ℓ]
    [(Appℓ _ _ ℓ) ℓ]
    [(ECAppℓ _ _ ℓ) ℓ]
    [(Setℓ _ _ ℓ) ℓ]
    [(Derefℓ _ ℓ) ℓ]
    [(Ifℓ _ _ _ ℓ) ℓ]
    [(ECSubElimDyn _ ℓ) ℓ]
    [_ #f]))

;; "file:line" of a term's own label, or "?" if it carries none. For error
;; messages that print a failing surface term and want to name its location.
(define (loc-of t)
  (define ℓ (term-label t))
  (if ℓ (unparse-label ℓ) "?"))

(define (unparse-meta-term term)
  (match term
    [(MFixAbs f x A B body)
     `(fixλ ,f (,x : ,(unparse-meta-type A)) : ,(unparse-meta-type B)
        ,(unparse-meta-term body))]
    [(MFixAbsℓ f x A B body ℓ)
     `(fixλ ,f (,x : ,(unparse-meta-type A)) : ,(unparse-meta-type B)
        ,(unparse-meta-term body) ,@(label-suffix ℓ))]
    [(MAbs x A body)
     `(λ (,x : ,(unparse-meta-type A))
        ,(unparse-meta-term body))]
    [(Cast M coerc) `(,(unparse-meta-term M) < ,(unparse-meta-hypercoercion coerc) >)]
    [(Blame A ℓ) `(blame ,(unparse-meta-type A) @ ,(unparse-label ℓ))]
    [(RefAnn term type) `(ref ,(unparse-meta-term term) :: ,(unparse-meta-type type))]
    [(Loc addr) `(& ,addr)]
    [(Quote Mᵒ ec) `(‶ ,(unparse-object-term Mᵒ) ″ ,(unparse-ec ec))]
    [(MVar x) (id->symbol x)]
    [(ECAbs α lb ub body)
     (define γ^ (if (not lb) '_ (unparse-ec lb)))
     (define β^ (if (not ub) '_ (unparse-ec ub)))
     `(Λ (,γ^ <: ,α <: ,β^) ,(unparse-meta-term body))]
    [(ECAbsCC α body)
     `(Λ ,α ,(unparse-meta-term body))]
    [(ECApp M ec) `(,(unparse-meta-term M) [,(unparse-ec ec)])]
    [(ECAppℓ M ec ℓ) `(,(unparse-meta-term M) [,(unparse-ec ec)] ,@(label-suffix ℓ))]
    [(ECSubIntro sub-ec sup-ec body)
     (define α (unparse-ec sub-ec))
     (define β (unparse-ec sup-ec))
     `(,α <: ,β ⇒ ,(unparse-meta-term body))]
    [(ECSubElim M) `(,(unparse-meta-term M) •)]
    [(ECSubElimDyn M ℓ) `(,(unparse-meta-term M) •⋆ ,@(label-suffix ℓ))]
    [(Ref M) `(ref ,(unparse-meta-term M))]
    [(Set M N) `(,(unparse-meta-term M) := ,(unparse-meta-term N))]
    [(Deref M) `(! ,(unparse-meta-term M))]
    [(Setℓ M N ℓ) `(,(unparse-meta-term M) := ,(unparse-meta-term N) ,@(label-suffix ℓ))]
    [(Derefℓ M ℓ) `(! ,(unparse-meta-term M) ,@(label-suffix ℓ))]
    [(LetStar bindings body)
     `(let* ,(map unparse-meta-binding bindings)
        ,(unparse-meta-term body))]
    [(Begin effects body)
     `(begin ,@(map unparse-meta-term effects)
             ,(unparse-meta-term body))]
    [_ (unparse-*-term unparse-meta-term term)]))

(define (unparse-meta-binding binding)
  (match binding
    [(LetBind var rhs)
     `(,(id->symbol var) ,(unparse-meta-term rhs))]
    [(LetBindTypeℓ var type rhs ℓ)
     `((,(id->symbol var) : ,(unparse-meta-type type)) ,(unparse-meta-term rhs) ,@(label-suffix ℓ))]
    [_ (error 'unparse-meta-binding "Invalid meta binding:~a" binding)]))

(define (Prim->type args-t ret-t)
  (for/foldr ([res (Base ret-t)])
    ([arg-t args-t])
    (Fun (Base arg-t) res)))

(define (unparse-object-term term)
  (match term
    [(or (OFixAbs α f β x T S body) (OFixAbsVal α f β x T S body))
     (define head-sym (if (OFixAbsVal? term) 'fixλ̅ 'fixλ))
     `(,head-sym ,(id->symbol α) ,(id->symbol f) ,(id->symbol β)
                 (,(id->symbol x) : ,(unparse-object-type T)) : ,(unparse-object-type S)
                 ,(unparse-object-term body))]
    [(OAbs α x T body)
     `(λ ,(id->symbol α) (,(id->symbol x) : ,(unparse-object-type T))
        ,(unparse-object-term body))]
    [(OVar x) (id->symbol x)]
    [(Splice M) `(~ ,(unparse-meta-term M))]
    [(Spliceℓ M ℓ) `(~ ,(unparse-meta-term M) ,@(label-suffix ℓ))]
    [(Asc Mᵒ T) `(,(unparse-object-term Mᵒ) :: ,(unparse-object-type T))]
    [(LetStar bindings body)
     `(let* ,(map unparse-object-binding bindings)
        ,(unparse-object-term body))]
    [(Blame S ℓ) `(blame ,(unparse-object-type S) @ ,(unparse-label ℓ))]
    [_ (unparse-*-term unparse-object-term term)]))

(define (unparse-object-binding binding)
  (match binding
    [(LetBind x rhs)
     `(,x ,(unparse-object-term rhs))]
    [(LetBindα x α rhs)
     `((,x ,α) ,(unparse-object-term rhs))]
    [(LetBindType x T rhs)
     `((,x : ,(unparse-object-type T)) ,(unparse-object-term rhs))]
    [(LetBindαType x α T rhs)
     `((,x : ,α ,(unparse-object-type T)) ,(unparse-object-term rhs))]
    [_ (error 'unparse-object-binding "Invalid object binding:~a" binding)]))

(define (unparse-*-term self term)
  (match term
    [(Const k)
     (cond
       [(or (symbol? k) (pair? k)) `',k]
       [else k])]
    [(App M N) `(,(self M) ,(self N))]
    [(If L M N) `(if ,(self L) ,(self M) ,(self N))]
    [(Prim args-t ret-t fun name) `(Prim ,name :: ,(unparse-object-type (Prim->type args-t ret-t)))]
    [(IfAnn L M N A) `(if ,(self L) ,(self M) ,(self N))]
    [(AppAnn L M A) `(,(self L) ,(self M))]
    [(Ifℓ L M N ℓ) `(if ,(self L) ,(self M) ,(self N) ,@(label-suffix ℓ))]
    [(Appℓ L M ℓ) `(,(self L) ,(self M) ,@(label-suffix ℓ))]
    [_ (error 'unparse-*-term "Invalid term: ~a" term)]))

(define (unparse-meta-hypercoercion hc)
  (unparse-*-hypercoercion hc
                           unparse-meta-hc-head
                           unparse-meta-hc-middle
                           unparse-meta-hc-tail))

(define (unparse-meta-hc-head h)
  (unparse-*-hc-head h unparse-meta-type 'meta))

(define (unparse-meta-hc-middle m)
  (define (recurse m^) (unparse-meta-hypercoercion m^))
  (match m
    [(CFun C1 C2) `(→ ,(recurse C1) ,(recurse C2))]
    [(CCode Cᵒ Cᵉ)
     `(‶ ,(unparse-object-hypercoercion Cᵒ) ″ ,(unparse-ec-hypercoercion Cᵉ))]
    [(CRefT write-C read-C)
     `(Ref ,(recurse write-C) ,(recurse read-C))]
    [(CECUniv α C)
     `(∀̇ ,α ,(unparse-meta-hypercoercion C))]
    [(CECSub sub-ec sup-ec C)
     (define α (unparse-ec sub-ec))
     (define β (unparse-ec sup-ec))
     `(,α <: ,β ⇒ ,(unparse-meta-hypercoercion C))]
    [(CId A) `(id ,(unparse-meta-type A))]
    [_ (unparse-*-hc-middle unparse-meta-hypercoercion m unparse-meta-type 'meta)]))

(define (unparse-meta-hc-tail t)
  (unparse-*-hc-tail t unparse-meta-type 'meta))

(define (unparse-object-hypercoercion hc)
  (unparse-*-hypercoercion hc
                           unparse-obj-hc-head
                           unparse-obj-hc-middle
                           unparse-obj-hc-tail))

(define (unparse-obj-hc-head h)
  (unparse-*-hc-head h unparse-object-type 'object))

(define (unparse-obj-hc-middle m)
  (unparse-*-hc-middle unparse-object-hypercoercion m unparse-object-type 'object))

(define (unparse-obj-hc-tail t)
  (unparse-*-hc-tail t unparse-object-type 'object))

(define (unparse-ec-hypercoercion hc)
  (unparse-*-hypercoercion hc
                           unparse-ec-hc-head
                           unparse-ec-hc-middle
                           unparse-ec-hc-tail))

(define (unparse-ec-hc-head h)
  (unparse-*-hc-head h unparse-ec 'ec))

(define (unparse-ec-hc-middle m)
  (match m
    [(CSub ec1 ec2) `(,(unparse-ec ec1) ↑ ,(unparse-ec ec2)) ]
    [(CBot ec1 ec2 ℓ) `(⊥ ,(unparse-ec ec1) ,(unparse-ec ec2) ,@(label-suffix ℓ))]
    [_ (error 'unparse-ec-hc-middle "Invalid EC hypercoercion middle: ~a" m)]))

(define (unparse-ec-hc-tail t)
  (unparse-*-hc-tail t unparse-ec 'ec))

(define (unparse-*-hypercoercion hc unparse-head unparse-middle unparse-tail)
  (match hc
    [(CHyp h m t) `(,(unparse-head h) ⁏ ,(unparse-middle m) ⁏ ,(unparse-tail t))]
    [_ (error 'unparse-*-hypercoercion "Invalid hypercoercion: ~a" hc)]))

(define (unparse-*-hc-head h unparse-field label)
  (match h
    [(CProj G ℓ) `(,(unparse-field G) ? ,@(label-suffix ℓ))]
    [(CId A) `(id ,(unparse-field A))]
    [_ (error 'unparse-*-hc-head "[~a]Invalid hypercoercion head: ~a" label h)]))

(define (unparse-*-hc-middle unparse-hyperc m unparse-field label)
  (match m
    [(CFun C1 C2) `(→ ,(unparse-hyperc C1) ,(unparse-hyperc C2))]
    [(CId A) `(id ,(unparse-field A))]
    [(CBot A B ℓ) `(⊥ ,(unparse-field A) ,(unparse-field B) ,@(label-suffix ℓ))]
    [_ (error 'unparse-*-hc-middle "[~a]Invalid hypercoercion middle: ~a" label m)]))

(define (unparse-*-hc-tail t unparse-field label)
  (match t
    [(CInj G) `(,(unparse-field G) !)]
    [(CId A) `(id ,(unparse-field A))]
    [_ (error 'unparse-*-hc-tail "[~a]Invalid hypercoercion tail: ~a" label t)]))

(define read-term
  (read-program-syntax
   (λ (p)
     (parse-meta-term
      (syntax-parse p
        #:datum-literals (program)
        [(program () body) #'body])))))
