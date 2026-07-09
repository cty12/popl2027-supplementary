#lang racket

(require graph)
(require racket/exn)
(require "ast.rkt")
(require "parse.rkt")
(require "utils.rkt")
(require (only-in  "sister-language/typecheck.rkt"
                   EC EC? OType MType
                   ecs-in-ctx
                   graph-⨆))
(require "sister-language/logging.rkt")

(provide (all-defined-out))

(define base-types
  (hasheqv
   'Bool boolean?
   'Int integer?
   'Str string?
   'Unit null?))

(define (maybe-base-type k)
  (for/or ([(type pred?) (in-dict base-types)])
    (cond
      [(pred? k) (Base type)]
      [else #f])))

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

(define (Prim->type arg-types ret-type name)
  (match arg-types
    ['()
     #:when (dict-has-key? base-types ret-type)
     (Base ret-type)]
    [`(,base . ,bases)
     #:when (dict-has-key? base-types base)
     (Fun (Base base) (Prim->type bases ret-type name))]
    [_
     (error 'Prim->type "Invalid primitive ~a with input types ~a and return type ~a"
            name arg-types ret-type)]))

(define primitives
  (hasheqv
   'zero? (Prim '(Int) 'Bool (lift-prim-1 zero?) 'zero?)
   'sub1 (Prim '(Int) 'Int (lift-prim-1 sub1) 'sub1)
   '+ (Prim '(Int Int) 'Int (lift-prim-2 +) '+)
   '- (Prim '(Int Int) 'Int (lift-prim-2 -) '-)
   '* (Prim '(Int Int) 'Int (lift-prim-2 *) '*)
   '/ (Prim '(Int Int) 'Int (lift-prim-2 quotient) '/)
   '% (Prim '(Int Int) 'Int (lift-prim-2 remainder) '%)))

(define prim-types
  (for/hasheqv ([(p-name prim) (in-dict primitives)])
    (match-define (Prim arg-types ret-type _ _) prim)
    (values p-name (Prim->type arg-types ret-type p-name))))

;; preconditions: For some ctx,
;;                (and (or (well-formed-ec? ec1 ctx) (eq? ec1 #f))
;;                     (or (well-formed-ec? ec2 ctx) (eq? ec2 #f))
;;                     (unweighted-graph? ec-subtypes))
(define (add-subtype ec-subtypes ec1 ec2)
  (match* (ec1 ec2)
    [(_ (ECEps)) #:when (not (ECEps? ec1))
     (error 'add-subtype "empty EC supertype")]
    [(#f (ECVar α))
     (define ec-subs^ (graph-copy ec-subtypes))
     (add-vertex! ec-subs^ α)
     ec-subs^]
    [((ECVar α) #f)
     (define ec-subs^ (graph-copy ec-subtypes))
     (add-vertex! ec-subs^ α)
     ec-subs^]
    [((ECVar α) (ECVar β)) #:when (not (eq? α β))
     (define ec-subs^ (graph-copy ec-subtypes))
     (add-vertex! ec-subs^ α)
     (add-vertex! ec-subs^ β)
     (add-directed-edge! ec-subs^ α β)
     ec-subs^]
    [((ECVar α) (ECVar β)) #:when (eq? α β)
     ec-subtypes]
    [((ECEps) _)
     ec-subtypes]
    [(_ _)
     (error 'add-subtype "unhandled case: ~a <: ~a" ec1 ec2)]
    ))

; Γ ⊢α Mᵒ ⇝ Pᵒ ⇒ T
(define (object-elaborate-synth ec term ctx ec-subtypes meta-uniq-vars obj-uniq-vars)
  (define (recurse term^)
    (object-elaborate-synth ec term^ ctx ec-subtypes meta-uniq-vars obj-uniq-vars))
  (define (obj-check term^ T)
    (object-elaborate-check ec term^ T ctx ec-subtypes meta-uniq-vars obj-uniq-vars))
  (match term
    [(Const k)
     (cond
       [(dict-has-key? prim-types k)
        (values term (dict-ref prim-types k))]
       [(maybe-base-type k) => (λ (type) (values term type))]
       [else (error 'object-elaborate-synth "Undefined object constant: ~a" k)])]
    [(OVar x)
     (unless (dict-has-key? obj-uniq-vars x) (error 'object-elaborate-synth "Undefined object variable: ~a" x))
     (define uniq-x (dict-ref obj-uniq-vars x))
     (match (dict-ref ctx uniq-x)
       [(OType T α)
        (unless (ec-≲ (ECVar α) ec ec-subtypes) (obj-elab-synth-err 'ovar-not-sub α x ec ec-subtypes))
        (values (OVar uniq-x) T)]
       [c (obj-elab-synth-err 'obj-var-not-otype x uniq-x c)])]
    [(OFixAbs α f β x S T Mᵒ)
     (when (ec-var-in-ctx? α ctx) (obj-elab-synth-err 'ec-param-exists α term))
     (when (ec-var-in-ctx? β ctx) (obj-elab-synth-err 'ec-param-exists β term))
     (define uniq-x (gen-id x))
     (define uniq-f (gen-id f))
     (define ctx^ (dict-set (dict-set ctx α (EC)) uniq-f (OType (Fun S T) α)))
     (define ctx^^ (dict-set (dict-set ctx^ β (EC)) uniq-x (OType S β)))
     (define ec-subtypes^ (add-subtype (add-subtype ec-subtypes ec (ECVar α)) (ECVar α) (ECVar β)))
     (define obj-uniq-vars^ (dict-set (dict-set obj-uniq-vars f uniq-f) x uniq-x))
     (define-values (Pᵒ T^)
       (object-elaborate-synth (ECVar β) Mᵒ ctx^^ ec-subtypes^ meta-uniq-vars obj-uniq-vars^))
     (unless (equal? T^ T) (obj-elab-synth-err 'ofixabs-return-type-mismatch T T^))
     (values (OFixAbs α uniq-f β uniq-x S T Pᵒ) (Fun S T))]
    [(OAbs α x S Mᵒ)
     (when (ec-var-in-ctx? α ctx) (obj-elab-synth-err 'ec-param-exists α term))
     (define uniq-x (gen-id x))
     (define ctx^ (dict-set (dict-set ctx α (EC)) uniq-x (OType S α)))
     (define ec-subtypes^ (add-subtype ec-subtypes ec (ECVar α)))
     (define obj-uniq-vars^ (dict-set obj-uniq-vars x uniq-x))
     (define-values (Pᵒ T)
       (object-elaborate-synth (ECVar α) Mᵒ ctx^ ec-subtypes^ meta-uniq-vars obj-uniq-vars^))
     (values (OFixAbs (gen-id '_) (gen-id '_) α uniq-x S T Pᵒ) (Fun S T))]
    [(App Lᵒ Mᵒ)
     (define-values (Qᵒ func-type) (recurse Lᵒ))
     (match func-type
       [(Fun S T)
        (define Pᵒ (obj-check Mᵒ S))
        (values (AppAnn Qᵒ Pᵒ T) T)]
       [fun-type (obj-elab-synth-err 'invalid-app-fun term fun-type)])]
    [(If Lᵒ Mᵒ Nᵒ)
     (define Rᵒ (obj-check Lᵒ (Base 'Bool)))
     (define-values (Pᵒ then-type) (recurse Mᵒ))
     (define-values (Qᵒ else-type) (recurse Nᵒ))
     (unless (equal? then-type else-type) (obj-elab-synth-err 'if-branches term then-type else-type))
     (values (IfAnn Rᵒ Pᵒ Qᵒ then-type) then-type)]
    [(Asc Mᵒ T)
     (define Pᵒ (obj-check Mᵒ T))
     (values Pᵒ T)]
    [(Spliceℓ _ _) (obj-elab-synth-err 'invalid-splice term)]
    [(LetStar bindings body)
     (define-values (body-ctx uniq-cc-bindings body-obj-uniqs body-surr-ec body-ec-subtypes)
       (for/fold ([ctx^ ctx] [uniq-binds '()] [obj-uniqs obj-uniq-vars] [surr-ec ec] [ec-subtypes^ ec-subtypes])
                 ([binding bindings])
         (define (accumulate x α T cc-rhs)
           (define uniq-x (gen-id x))
           (values
             (dict-set (dict-set ctx^ α (EC)) uniq-x (OType T α))
             (append uniq-binds (list (LetBindαType uniq-x α T cc-rhs)))
             (dict-set obj-uniqs x uniq-x)
             (ECVar α)
             (add-subtype ec-subtypes^ surr-ec (ECVar α))))
         (match binding
           [(LetBind x Mᵒ)
            (define-values (Pᵒ T)
              (object-elaborate-synth surr-ec Mᵒ ctx^ ec-subtypes^ meta-uniq-vars obj-uniqs))
            (define α (gen-id 'letα))
            (accumulate x α T Pᵒ)]
           [(LetBindType x T Mᵒ)
            (define Pᵒ (object-elaborate-check surr-ec Mᵒ T ctx^ ec-subtypes^ meta-uniq-vars obj-uniqs))
            (define α (gen-id 'letα))
            (accumulate x α T Pᵒ)]
           [(LetBindα x α Mᵒ)
            (define-values (Pᵒ T)
              (object-elaborate-synth surr-ec Mᵒ ctx^ ec-subtypes^ meta-uniq-vars obj-uniqs))
            (accumulate x α T Pᵒ)]
           [(LetBindαType x α T Mᵒ)
            (define Pᵒ (object-elaborate-check surr-ec Mᵒ T ctx^ ec-subtypes^ meta-uniq-vars obj-uniqs))
            (accumulate x α T Pᵒ)])))
     (define-values (cc-body body-type)
       (object-elaborate-synth body-surr-ec body body-ctx body-ec-subtypes meta-uniq-vars body-obj-uniqs))
     (define elab-term
       (for/foldr ([Pᵒ cc-body])
                  ([binding uniq-cc-bindings])
         (match binding
           [(LetBindαType uniq-x α rhs-type cc-rhs)
            (AppAnn (OFixAbs (gen-id '_) (gen-id '_) α uniq-x rhs-type body-type Pᵒ) cc-rhs body-type)])))
     (values elab-term body-type)]
    [_ (obj-elab-synth-err 'invalid-term term)]))

(define (ec-var-in-ctx? α ctx)
  (and (dict-has-key? ctx α)
       (EC? (dict-ref ctx α))))

(define (well-formed-ec? ec ctx)
  (match ec
    [(Dyn) #t]
    [_ (well-formed-static-ec? ec ctx)]))

(define (well-formed-static-ec? ec ctx)
  (match ec
    [(ECVar α)
     (ec-var-in-ctx? α ctx)]
    [(ECEps)
     #t]
    [else
     #f]))

; Γ ⊢α Mᵒ ⇝ Pᵒ ⇐ T
(define (object-elaborate-check ec term type ctx ec-subtypes meta-uniq-vars obj-uniq-vars)
  (match term
    [(Spliceℓ M ℓ)
     (define-values (P A) (meta-elaborate M ctx ec-subtypes meta-uniq-vars obj-uniq-vars))
     (define B (Code type ec))
     (unless (meta-type-≲ A B ctx ec-subtypes) (obj-elab-check-err 'splice-not-subtype term A B ec-subtypes))
     (Splice (cast-meta P A B ℓ))]
    [term
     (define-values (Pᵒ T) (object-elaborate-synth ec term ctx ec-subtypes meta-uniq-vars obj-uniq-vars))
     (unless (equal? T type) (obj-elab-check-err 'type-mismatch term type T))
     Pᵒ]
    [_ (error 'object-elaborate-check "Cannot handle term:~n~v~n" term)]))

; Γ ⊢ M ⇝ P : A
(define (meta-elaborate term [ctx (hash)]
                        [ec-subtypes (unweighted-graph/directed '())]
                        [meta-uniq-vars (hash)]
                        [obj-uniq-vars (hash)])
  (define (recurse term^)
    (meta-elaborate term^ ctx ec-subtypes meta-uniq-vars obj-uniq-vars))
  (match term
    [(Const k)
     (cond
       [(dict-has-key? prim-types k)
        (values (dict-ref primitives k) (dict-ref prim-types k))]
       [(maybe-base-type k) => (λ (type) (values term type))]
       [else
        (error 'meta-elaborate "Undefined meta constant: ~a" k)])]
    [(MVar x)
     (unless (dict-has-key? meta-uniq-vars x) (error 'meta-elaborate "Undefined meta variable: ~a" x))
     (define uniq-x (dict-ref meta-uniq-vars x))
     (match (dict-ref ctx uniq-x)
       [(MType A) (values (MVar uniq-x) A)]
       [c (meta-elaborate-err 'mvar-not-mtype x uniq-x c)])]
    [(MFixAbsℓ f x A B M ℓ)
     (unless (well-formed-meta-type? A ctx) (meta-elaborate-err 'ill-formed-param-type term A))
     (unless (well-formed-meta-type? B ctx) (meta-elaborate-err 'ill-formed-return-type term B))
     (define uniq-x (gen-id x))
     (define uniq-f (gen-id f))
     (define ctx^ (dict-set (dict-set ctx uniq-x (MType A)) uniq-f (MType (Fun A B))))
     (define meta-uniq-vars^ (dict-set (dict-set meta-uniq-vars x uniq-x) f uniq-f))
     (define-values (P B^) (meta-elaborate M ctx^ ec-subtypes meta-uniq-vars^ obj-uniq-vars))
     (unless (meta-type-≲ B^ B ctx ec-subtypes) (meta-elaborate-err 'return-type-not-subtype term B B^))
     (define A-cc (surface->cc-type A))
     (define B-cc (surface->cc-type B))
     (values (MFixAbs uniq-f uniq-x A-cc B-cc (cast-meta P B^ B ℓ)) (Fun A B))]
    [(MAbs x A M)
     (unless (well-formed-meta-type? A ctx) (meta-elaborate-err 'ill-formed-param-type term A))
     (define uniq-x (gen-id x))
     (define ctx^ (dict-set ctx uniq-x (MType A)))
     (define-values (P B)
       (meta-elaborate M ctx^ ec-subtypes (dict-set meta-uniq-vars x uniq-x) obj-uniq-vars))
     (define A-cc (surface->cc-type A))
     (define B-cc (surface->cc-type B))
     (values (MFixAbs (gen-id 'f) uniq-x A-cc B-cc P) (Fun A B))]
    [(Appℓ L M ℓ)
     (define-values (Q Q-type) (recurse L))
     (define-values (P P-type) (recurse M))
     (match Q-type
       [(Fun A A^)
        (unless (meta-type-≲ P-type A ctx ec-subtypes) (meta-elaborate-err 'app-arg-not-subtype term P-type A))
        (values (App Q (cast-meta P P-type A ℓ)) A^)]
       [(Dyn)
        (values (App (cast-meta Q (Dyn) (Fun (Dyn) (Dyn)) ℓ)
                     (cast-meta P P-type (Dyn) ℓ))
                (Dyn))]
       [_ (meta-elaborate-err 'invalid-app-fun-type term Q-type)])]
    [(ECAbs α lb ub M)
     (unless (if lb (well-formed-static-ec? lb ctx) #t) (meta-elaborate-err 'ill-formed-static-ec term lb ctx))
     (unless (if ub (well-formed-static-ec? ub ctx) #t) (meta-elaborate-err 'ill-formed-static-ec term ub ctx))
     (when (ec-var-in-ctx? α ctx) (meta-elaborate-err 'ec-param-exists α term))
     (define ec-subtypes^ (add-subtype (add-subtype ec-subtypes (ECVar α) ub) lb (ECVar α)))
     (define-values (P P-type)
       (meta-elaborate M (dict-set ctx α (EC)) ec-subtypes^ meta-uniq-vars obj-uniq-vars))
     (define ec-α (ECVar α))
     (define ec-lb (or lb ec-α))
     (define ec-ub (or ub ec-α))
     (values (ECAbsCC α
                      (ECSubIntro ec-lb ec-α
                                  (ECSubIntro ec-α ec-ub
                                              P)))
             (ECUniv α lb ub P-type))]
    [(ECAppℓ M ec ℓ)
     (unless (well-formed-static-ec? ec ctx) (meta-elaborate-err 'ill-formed-static-ec term ec ctx))
     (define-values (P P-type) (recurse M))
     (match P-type
       [(ECUniv α lb ub A)
        (unless (if ub (ec-<: ec ub ec-subtypes) #t) (meta-elaborate-err 'fail-ecapp-ub term ec P-type))
        (unless (if lb (ec-<: lb ec ec-subtypes) #t) (meta-elaborate-err 'fail-ecapp-lb term ec P-type))
        (values (ECSubElim (ECSubElim (ECApp P ec)))
                (type-ec-rename A α ec))]
       [(Dyn)
        (values (ECSubElimDyn (ECSubElimDyn
                               (ECApp (Cast P (coerce-meta (Dyn) (ECUnivCC (gen-id '_) (Dyn)) ℓ))
                                      ec) ℓ) ℓ)
                (Dyn))]
       [_ (meta-elaborate-err 'invalid-ecapp-type term P-type)])]
    [(Quote Mᵒ ec)
     (unless (well-formed-static-ec? ec ctx) (meta-elaborate-err 'ill-formed-static-ec term ec ctx))
     (define-values (Pᵒ T) (object-elaborate-synth ec Mᵒ ctx ec-subtypes meta-uniq-vars obj-uniq-vars))
     (values (Quote Pᵒ ec) (Code T ec))]
    [(Ref M)
     (define-values (P A) (recurse M))
     (values (RefAnn P A) (RefT A))]
    [(Setℓ L M ℓ)
     (define-values (Q Q-type) (recurse L))
     (define-values (P P-type) (recurse M))
     (match Q-type
       [(RefT A)
        (unless (meta-type-≲ P-type A ctx ec-subtypes) (meta-elaborate-err 'invalid-set-subtype term P-type A))
        (values (Set Q (cast-meta P P-type A ℓ)) (Base 'Unit))]
       [(Dyn)
        (values (Set (cast-meta Q (Dyn) (RefT (Dyn)) ℓ)
                     (cast-meta P P-type (Dyn) ℓ))
                (Base 'Unit))]
       [_ (meta-elaborate-err 'invalid-set-lhs-type term Q-type)])]
    [(Derefℓ M ℓ)
     (define-values (P P-type) (recurse M))
     (match P-type
       [(RefT A)
        (values (Deref P) A)]
       [(Dyn)
        (values (Deref (cast-meta P (Dyn) (RefT (Dyn)) ℓ)) (Dyn))]
       [_ (meta-elaborate-err 'invalid-deref-type term P-type)])]
    [(Ifℓ L M N ℓ)
     (define-values (Q A) (recurse L))
     (unless (meta-type-≲ A (Base 'Bool) ctx ec-subtypes) (meta-elaborate-err 'if-test-not-bool term A))
     (define-values (P B₁) (recurse M))
     (define-values (R B₂) (recurse N))
     (define B (meta-type-⋁̃ B₁ B₂ ctx ec-subtypes))
     (values (IfAnn (cast-meta Q A (Base 'Bool) ℓ)
                    (cast-meta P B₁ B ℓ)
                    (cast-meta R B₂ B ℓ)
                    (surface->cc-type B))
             B)]
    [(Begin effects body)
     (define-values (cc-body body-type) (recurse body))
     (define cc-body-type (surface->cc-type body-type))
     (define elab-term
       (for/foldr ([P cc-body])
                  ([M effects])
         (define-values (cc-eff eff-type) (recurse M))
         (define cc-eff-type (surface->cc-type eff-type))
         (App (MFixAbs (gen-id '_) (gen-id '_) cc-eff-type cc-body-type P) cc-eff)))
     (values elab-term body-type)]
    [(LetStar bindings body)
     (define-values (body-ctx uniq-cc-bindings body-meta-uniqs)
       (for/fold ([ctx^ ctx] [uniq-binds '()] [meta-uniqs meta-uniq-vars])
                 ([binding bindings])
         (define (accumulate x A cc-rhs)
           (define uniq-x (gen-id x))
           (define cc-rhs-type (surface->cc-type A))
           (values
            (dict-set ctx^ uniq-x (MType A))
            (append uniq-binds (list (LetBindType uniq-x cc-rhs-type cc-rhs)))
            (dict-set meta-uniqs x uniq-x)))
         (match binding
           [(LetBind x M)
            (define-values (P A) (meta-elaborate M ctx^ ec-subtypes meta-uniqs obj-uniq-vars))
            (accumulate x A P)]
           [(LetBindTypeℓ x A M ℓ)
            (define-values (P A^) (meta-elaborate M ctx^ ec-subtypes meta-uniqs obj-uniq-vars))
            (unless (meta-type-≲ A^ A ctx^ ec-subtypes) (meta-elaborate-err 'bad-let-ann binding A A^))
            (accumulate x A (cast-meta P A^ A ℓ))])))
     (define-values (cc-body body-type)
       (meta-elaborate body body-ctx ec-subtypes body-meta-uniqs obj-uniq-vars))
     (define cc-body-type (surface->cc-type body-type))
     (define elab-term
       (for/foldr ([P cc-body])
         ([binding uniq-cc-bindings])
         (match binding
           [(LetBindType uniq-x cc-rhs-type cc-rhs)
            (App (MFixAbs (gen-id '_) uniq-x cc-rhs-type cc-body-type P) cc-rhs)])))
     (values elab-term body-type)]
    [_ (error 'meta-elaborate "Cannot handle term:~n~v~n" term)]))

(define (ec-≲ ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [((Dyn) _) #t]
    [(_ (Dyn)) #t]
    [((ECEps) _) #t]
    [((ECVar α) (ECVar β))
     (ec-<: ec1 ec2 ec-subtypes)]
    [(_ _) #f]
    ))

;; Γ ⊢ α <: β
;; precondition: ∃ ctx,
;;               (and (well-formed-static-ec? ec1 ctx)
;;                    (well-formed-static-ec? ec2 ctx))
(define (ec-<: ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [((ECEps) _) #t]
    [((ECVar α) (ECVar β))
     (or (equal? α β)
         (and
          (has-vertex? ec-subtypes α)
          (has-vertex? ec-subtypes β)
          (not (eqv? (fewest-vertices-path ec-subtypes α β) #f)))) ;; ax + trans
     ]
    [(_ _) #f]))

(define (meta-type-≲ type1 type2 [ctx (hash)]
                     [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse-≲ A B)
    (meta-type-≲ A B ctx ec-subtypes))
  (match* (type1 type2)
    [((Dyn) _) #t]
    [(_ (Dyn)) #t]
    [((Base ι) (Base ι^)) (eqv? ι ι^)]
    [((Fun A B) (Fun A^ B^))
     (and (recurse-≲ A^ A) (recurse-≲ B B^))]
    [((RefT A) (RefT B))
     (and (meta-type-≲ A B ec-subtypes)
          (meta-type-≲ B A ec-subtypes))]
    [((Code O ec1) (Code O^ ec2))
     (and (object-type-≲ O O^)
          (ec-≲ ec1 ec2 ec-subtypes))]
    [((ECUniv α lb ub A) (ECUniv β lb^ ub^ B))
     (define α^ (gen-id 'α))
     (and (equal? lb lb^)
          (equal? ub ub^)
          (meta-type-≲ (type-ec-rename A α (ECVar α^))
                       (type-ec-rename B β (ECVar α^))
                       (dict-set ctx α^ (EC))
                       (add-subtype (add-subtype ec-subtypes (ECVar α^) ub)
                                    lb (ECVar α^))))]
    [(_ _)
     #f]))

(define (object-type-≲ type1 type2)
  (define (recurse-≲ A B)
    (object-type-≲ A B))
  (match* (type1 type2)
    [((Dyn) _)
     #t]
    [(_ (Dyn))
     #t]
    [((Base ι) (Base ι^))
     (eqv? ι ι^)]
    [((Fun A B) (Fun A^ B^))
     (and (recurse-≲ A^ A) (recurse-≲ B B^))]
    [(_ _)
     #f]))

(define (well-formed-meta-type? type [ctx (hash)])
  (match type
    [(Dyn)
     ;; wf-dyn
     #t]
    [(Base b)
     ;; wf-base
     #t]
    [(Fun A B)
     ;; wf-fun
     (and (well-formed-meta-type? A ctx)
          (well-formed-meta-type? B ctx))]
    [(RefT A)
     ;; wf-ref
     (well-formed-meta-type? A ctx)]
    [(Code T ec)
     ;; wf-code
     (cond
       [(well-formed-ec? ec ctx) #t]
       [else
        (well-formed-meta-type?-log 'ill-formed-ec type ec ctx)
        #f])]
    [(ECUniv α lb ub A)
     ;; wf-univ
     (cond
       [(ec-var-in-ctx? α ctx)
        (well-formed-meta-type?-log 'ec-param-exists type α ctx)
        #f]
       [(not (if ub (well-formed-static-ec? ub ctx) #t))
        (well-formed-meta-type?-log 'ill-formed-static-ub type ub ctx)
        #f]
       [(not (if lb (well-formed-static-ec? lb ctx) #t))
        (well-formed-meta-type?-log 'ill-formed-static-lb type lb ctx)
        #f]
       [else (well-formed-meta-type? A (dict-set ctx α (EC)))])]
    [_ (error 'well-formed-meta-type? "Invalid meta type: ~a" type)]))

(define (meta-type-⋁̃ type1 type2 [ctx (hash)]
                     [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse-⋁̃ A B) (meta-type-⋁̃ A B ctx ec-subtypes))
  (match* (type1 type2)
    [((Dyn) _) (Dyn)]
    [(_ (Dyn)) (Dyn)]
    [((Base ι) (Base ι^)) #:when (equal? ι ι^) (Base ι)]
    [((Fun A B) (Fun A^ B^))
     (Fun (meta-type-⋀̃ A^ A ctx ec-subtypes) (recurse-⋁̃ B B^))]
    [((RefT A) (RefT B))
     (unless (meta-type-α-equiv? A B) (meta-type-⋁̃-err 'ref-not-same type1 type2))
     (RefT A)]
    [((Code T ec1) (Code T^ ec2))
     (handle-code-⋁̃ type1 type2 (λ ()
       (Code (object-type-⋁̃ T T^) (ec-⋁̃ ec1 ec2 ec-subtypes))))]
    [((ECUniv α lb ub A) (ECUniv β lb^ ub^ B))
     #:when (equal? lb lb^) (equal? ub ub^)
     (define α^ (gen-id 'α))
     (define ec-α^ (ECVar α^))
     (ECUniv α^ lb ub
             (meta-type-⋁̃ (type-ec-rename A α ec-α^)
                          (type-ec-rename B β ec-α^)
                          (dict-set ctx α^ (EC))
                          (add-subtype (add-subtype ec-subtypes lb ec-α^) ec-α^ ub)))]
    [(_ _) (meta-type-⋁̃-err 'incomparable-types type1 type2)]))

(define (ec-⋁̃ ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [(_ (Dyn)) (Dyn)]
    [((Dyn) _) (Dyn)]
    [(_ _) (ec-⋁ ec1 ec2 ec-subtypes)]))

;; Γ ⊢ α ⋁ β = γ
;; precondition: ∃ ctx,
;;               (and (well-formed-static-ec? ec1 ctx)
;;                    (well-formed-static-ec? ec2 ctx))
(define (ec-⋁ ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [(_ (ECEps))
     ec1]
    [((ECEps) _)
     ec2]
    [((ECVar α) (ECVar β)) #:when (equal? α β)
     (ECVar α)]
    [((ECVar α) (ECVar β))
     ;; ec-⋁-traverse
     (define ⋁ (graph-⨆ α β ec-subtypes))
     (match (length ⋁)
       [0 (error 'ec-⋁ "No least upper bound found for ~a and ~a.~nSubtypes: ~a"
                 ec1 ec2 (get-edges ec-subtypes))]
       [1 (ECVar (car ⋁))]
       [_ (error 'ec-⋁ "Multiple least upper bounds found for ~a and ~a.~nLUB candidates: ~a~nSubtypes: ~a"
                 α β ⋁ (get-edges ec-subtypes))])]))

(define (object-type-⋁̃ type1 type2)
  (match* (type1 type2)
    [((Dyn) _) (Dyn)]
    [(_ (Dyn)) (Dyn)]
    [((Base ι) (Base ι^)) #:when (equal? ι ι^) (Base ι)]
    [((Fun A B) (Fun A^ B^))
     (Fun (object-type-⋀̃ A^ A) (object-type-⋁̃ B B^))]
    [(_ _) (error 'object-type-⋁̃ "Cannot find least upper bound for types ~a and ~a" type1 type2)]))

(define (meta-type-⋀̃ type1 type2 [ctx (hash)]
                     [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse-⋀̃ A B)
    (meta-type-⋀̃ A B ctx ec-subtypes))
  (match* (type1 type2)
    [((Dyn) _) type2]
    [(_ (Dyn)) type1]
    [((Base ι) (Base ι^)) #:when (equal? ι ι^) (Base ι)]
    [((Fun A B) (Fun A^ B^))
     (Fun (meta-type-⋁̃ A^ A ctx ec-subtypes) (recurse-⋀̃ B B^))]
    [((RefT A) (RefT B))
     (unless (meta-type-α-equiv? A B) (meta-type-⋀̃-err 'ref-not-same type1 type2))
     (RefT A)]
    [((Code T ec1) (Code T^ ec2))
     (handle-code-⋀̃ type1 type2 (λ ()
       (Code (object-type-⋀̃ T T^) (ec-⋀̃ ec1 ec2 ec-subtypes))))]
    [((ECUniv α lb ub A) (ECUniv β lb^ ub^ B))
     #:when (and (equal? lb lb^) (equal? ub ub^))
     (define α^ (gen-id 'α))
     (ECUniv α^ lb^ ub^
             (meta-type-⋀̃ (type-ec-rename A α (ECVar α^))
                   (type-ec-rename B β (ECVar α^))
                   (dict-set ctx α^ (EC))
                   (add-subtype (add-subtype ec-subtypes lb^ (ECVar α^))
                                (ECVar α^) ub^)))]
    [(_ _) (meta-type-⋀̃-err 'incomparable-types type1 type2)]))

(define (ec-⋀̃ ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [(_ (Dyn)) (Dyn)]
    [((Dyn) _) (Dyn)]
    [(_ _) (ec-⋀ ec1 ec2 ec-subtypes)]))

;; Γ ⊢ α ⋀ β = γ
;; precondition: ∃ ctx,
;;               (and (well-formed-ec? ec1 ctx)
;;                    (well-formed-ec? ec2 ctx))
(define (ec-⋀ ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [((ECEps) _)
     (ECEps)]
    [(_ (ECEps))
     (ECEps)]
    [((ECVar α) (ECVar β)) #:when (equal? α β)
     ;; ec-⋀-self
     (ECVar α)]
    [((ECVar α) (ECVar β))
     ;; ec-⋀-traverse
     (define ⋀ (graph-⨆ α β (transpose ec-subtypes)))
     (match (length ⋀)
       [0 (ECEps)]
       [1 (ECVar (car ⋀))]
       [_ (error 'ec-⋀ "Multiple greatest lower bounds found for ~a and ~a.~nGLB candidates: ~a~nSubtypes: ~a"
                 α β ⋀ (get-edges ec-subtypes))])]))

(define (object-type-⋀̃ type1 type2)
  (match* (type1 type2)
    [((Dyn) _) (Dyn)]
    [(_ (Dyn)) (Dyn)]
    [((Base ι) (Base ι^)) #:when (equal? ι ι^) (Base ι)]
    [((Fun A B) (Fun A^ B^))
     (Fun (object-type-⋁̃ A^ A) (object-type-⋀̃ B B^))]
    [(_ _) (error 'object-type-⋀̃ "Cannot find greatest lower bound for types ~a and ~a" type1 type2)]))


;; precondition: (meta-type-≲ src-type tgt-type)
(define (cast-meta exp src-type tgt-type ℓ)
  (cond [(meta-type-α-equiv? src-type tgt-type)
         exp]
        [else
         (Cast exp (coerce-meta (surface->cc-type src-type)
                                (surface->cc-type tgt-type)
                                ℓ))]))
   
;; Create a hyper-coercion between two cast calculus meta types
(define (coerce-meta src-type tgt-type ℓ)
  (match* (src-type tgt-type)
    [((Base ι1) (Base ι2)) #:when (eqv? ι1 ι2)
     (let ([id (CId (Base ι1))])
       (CHyp id id id))]
    [((Dyn) (Dyn))
     (let ([id (CId (Dyn))])
       (CHyp id id id))]
    [((Dyn) _) #:when (ground-type? tgt-type)
     (CHyp (CProj tgt-type ℓ) (ground-id tgt-type) (CId tgt-type))]
    [((Dyn) _)
     (define G (to-ground-type tgt-type))
     (match (coerce-meta G tgt-type ℓ)
        [(CHyp _ m t)
         (CHyp (CProj G ℓ) m t)])]
    [(_ (Dyn)) #:when (ground-type? src-type)
     (CHyp (CId src-type) (ground-id src-type) (CInj src-type))]
    [(_ (Dyn))
     (define G (to-ground-type src-type))
     (match (coerce-meta src-type G ℓ)
        [(CHyp h m _)
         (CHyp h m (CInj G))])]
    [((Fun A B) (Fun A^ B^))
     (CHyp (CId (Fun A B))
           (CFun (coerce-meta A^ A ℓ) (coerce-meta B B^ ℓ))
           (CId (Fun A^ B^)))]
    [((RefT A) (RefT B))
     (CHyp (CId (RefT A))
           (CRefT (coerce-meta B A ℓ) (coerce-meta A B ℓ))
           (CId (RefT B)))]
    [((Code O eĉ1) (Code O^ eĉ2))
     (CHyp (CId (Code O eĉ1))
           (CCode (coerce-object O O^ ℓ) (coerce-ec eĉ1 eĉ2 ℓ))
           (CId (Code O^ eĉ2)))]
    [((ECUnivCC α A) (ECUnivCC α^ A^))
     (define fresh-α (gen-id α))
     (CHyp (CId (ECUnivCC α A))
           (CECUniv fresh-α (coerce-meta (type-ec-rename A α (ECVar fresh-α))
                                         (type-ec-rename A^ α^ (ECVar fresh-α))
                                         ℓ))
           (CId (ECUnivCC α^ A^)))]
    [((ECSub sub-ec1 sup-ec1 A) (ECSub sub-ec2 sup-ec2 B))
     #:when (and (equal? sub-ec1 sub-ec2) (equal? sup-ec1 sup-ec2))
     (CHyp (CId (ECSub sub-ec1 sup-ec1 A))
           (CECSub sub-ec1 sup-ec1 (coerce-meta A B ℓ))
           (CId (ECSub sub-ec1 sup-ec1 B)))]
    [(_ _)
     (error 'coerce-meta "Failed to coerce from meta type ~a to meta type ~a"
            (unparse-meta-type src-type) (unparse-meta-type tgt-type))]))

;; precondition: type is a valid meta or object ground type
;; postcondition: · ⊢ (ground-id ground) : ground ⇒ ground
(define (ground-id ground)
  (define id⋆ (CHyp (CId (Dyn)) (CId (Dyn)) (CId (Dyn))))
  (match ground
    [(Base ι)
     (CId (Base ι))]
    [(Fun (Dyn) (Dyn))
     (CFun id⋆ id⋆)]
    [(RefT (Dyn))
     (CRefT id⋆ id⋆)]
    [(Code (Dyn) (Dyn))
     (CCode id⋆ (CHyp (CId (Dyn)) (CSub (Dyn) (Dyn)) (CId (Dyn))))]
    [(ECUnivCC α (Dyn))
     (define fresh-α (gen-id α))
     (CECUniv fresh-α id⋆)]
    [(ECSub sub-ec sup-ec (Dyn))
     (CECSub sub-ec sup-ec id⋆)]
    [_ (error 'ground-id "Invalid ground type: ~a" (unparse-meta-type ground))]))

;; Create a hyper-coercion between two objects types

;; precondition: (and (or (object-type? src-type) (equal? src-type (Dyn)))
;;                    (or (object-type? tgt-type) (equal? tgt-type (Dyn))))
(define (coerce-object src-type tgt-type ℓ)
  (match* (src-type tgt-type)
    [((Base ι1) (Base ι2)) #:when (eqv? ι1 ι2)
     (let ([id (CId (Base ι1))])
       (CHyp id id id))]
    [((Dyn) (Dyn))
     (let ([id (CId (Dyn))])
       (CHyp id id id))]
    [((Dyn) _) #:when (ground-type? tgt-type)
     (CHyp (CProj tgt-type ℓ) (ground-id tgt-type) (CId tgt-type))]
    [((Dyn) _)
     (define G (to-ground-type tgt-type))
     (match (coerce-object G tgt-type ℓ)
        [(CHyp _ m t)
         (CHyp (CProj G ℓ) m t)])]
    [(_ (Dyn)) #:when (ground-type? src-type)
     (CHyp (CId src-type) (ground-id src-type) (CInj src-type))]
    [(_ (Dyn))
     (define G (to-ground-type src-type))
     (match (coerce-object src-type G ℓ)
        [(CHyp h m _)
         (CHyp h m (CInj G))])]
    [((Fun A B) (Fun A^ B^))
     (CHyp (CId (Fun A B))
           (CFun (coerce-object A^ A ℓ) (coerce-object B B^ ℓ))
           (CId (Fun A^ B^)))]
    ))

#;
(define (maybe-id? v)
  (or (eqv? v #f) (id? v)))

(define (ground-type? type)
  (match type
    [(or
      (Base _)
      (Fun (Dyn) (Dyn))
      (RefT (Dyn))
      (Code (Dyn) (Dyn))
      (ECUnivCC (? id?) (Dyn))
      (ECSub _ _ (Dyn)))
     #t]
    [_ #f]))

(define (to-ground-type type)
  (match type
      [(Base _) type]
      [(Fun _ _) (Fun (Dyn) (Dyn))]
      [(RefT _) (RefT (Dyn))]
      [(Code _ _) (Code (Dyn) (Dyn))]
      [(ECUnivCC α _) (ECUnivCC α (Dyn))]
      [(ECSub sub-ec sup-ec _) (ECSub sub-ec sup-ec (Dyn))]
      [_ (error 'meta->ground-type "Not a meta type: ~a" type)]))

;; Creat a hyper-coercion between two environment classifiers

;; precondition: (ec-≲ src-ec tgt-ec)
;; postcondition: (equal? (ec-coercion-typecheck
;;                          (coerce-ec src-ec tgt-ec))
;;                        (values src-ec tgt-ec))
(define (coerce-ec src-ec tgt-ec ℓ)
  (match* (src-ec tgt-ec)
    [((Dyn) (Dyn))
     (let ([id (CId (Dyn))])
       (CHyp id (CSub (Dyn) (Dyn)) id))]
    [(_ (Dyn))
     (CHyp (CId src-ec)
           (CSub src-ec src-ec)
           (CInj src-ec))]
    [((Dyn) _)
     (CHyp (CProj tgt-ec ℓ)
           (CSub tgt-ec tgt-ec)
           (CId tgt-ec))]
    [(e e^)
     (CHyp (CId e)
           (CSub e e^)
           (CId e^))]
    [(_ _) (error 'coerce-ec "Failed to coerce from EC ~a to EC ~a" src-ec tgt-ec)]))

(define (surface->cc-type type)
  (match type
    [(Dyn) (Dyn)]
    [(Base b) (Base b)]
    [(Fun A B)
     (Fun (surface->cc-type A) (surface->cc-type B))]
    [(RefT A)
     (RefT (surface->cc-type A))]
    [(Code T ec) (Code T ec)]
    [(ECUniv α lb ub A)
     (define ec-α (ECVar α))
     (define ec-lb (or lb ec-α))
     (define ec-ub (or ub ec-α))
     (ECUnivCC α (ECSub ec-lb ec-α (ECSub ec-α ec-ub (surface->cc-type A))))]
    [_ (error 'surface->cc-type "Invalid surface meta type: ~a" type)]))

(define (obj-elab-synth-err key . args)
  (match* (key args)
    [('ovar-not-sub (list α x ec ec-subtypes))
     (error
      'object-elaborate-synth
      (string-append
       "The environment classifier ~a associated with object variable ~a"
       " was expected to be a consistent subtype of ~a, but it "
       "actually is not.~nSubtypes: ~a~n")
      α x ec (get-edges ec-subtypes))]
    [('obj-var-not-otype (list x uniq-x c))
     (error
      'object-elaborate-synth
      "Object variable ~a (unique name ~a) expected to be an object type but got ~a.~n"
      x uniq-x c)]
    [('ofixabs-return-type-mismatch (list T T^))
     (error 'object-elaborate-synth
            (string-append
             "In object fixpoint lambda:~n~v~nThe given return type ~a and actual "
             "type returned ~a are not the same")
            (unparse-object-type T)
            (unparse-object-type T^))]
    [('ec-param-exists (list α term))
     (error 'object-elaborate-synth
            (string-append
             "In term:~n~v~nEnvironment classifier parameter ~a is already used in "
             "scope. Use a fresh classifier name.")
            (id->symbol α) (unparse-object-term term))]
    [('invalid-app-fun (list term fun-type))
     (error 'object-elaborate-synth
            (string-append
             "In term:~n~v~nType of the function in application"
             "should be a function, but found:\n\t~a")
            (unparse-object-term term)
            (unparse-object-type fun-type))]
    [('if-branches (list term then-type else-type))
     (error 'object-elaborate-synth
            (string-append
             "In term:~n~v~nType of the then branch ~a and else branch ~a should "
             "be the same")
            (unparse-object-term term)
            (unparse-object-type then-type)
            (unparse-object-type else-type))]
    [('invalid-splice `(,term))
     (error 'object-elaborate-synth
            (string-append
             "In term:~n~v~nCannot synthesize a type for splice term. "
             "Try ascribing a type to the term")
            (unparse-object-term term))]
    [('invalid-term `(,term))
     (error 'object-elaborate-synth "Cannot handle term:~n~v~n" term)]))

(define (obj-elab-check-err key . args)
  (match* (key args)
    [('splice-not-subtype (list term A B ec-subtypes))
     (error 'object-elaborate-check
            (string-append
             "In term at ~a:~n~v~nThe type of the spliced term ~a should be a "
             "consistent subtype of ~a" "~nwith subtypes~n~a")
            (loc-of term)
            (unparse-object-term term)
            (unparse-meta-type A)
            (unparse-meta-type B)
            (get-edges ec-subtypes))]
    [('type-mismatch (list term type T))
     (error 'object-elaborate-check
            "In:~n~v~n checked type ~a is not equal to synthesized type ~a"
            (unparse-object-term term) (unparse-object-type type)
            (unparse-object-type T))]))

(define (meta-elaborate-err key . args)
  (match* (key args)
    [('mvar-not-mtype (list x uniq-x c))
     (error
      'meta-elaborate
      "Meta variable ~a (unique name ~a) expected to be of meta type but got ~a.~n"
      x uniq-x c)]
    [('ill-formed-return-type (list term B))
     (error
      'meta-elaborate
      (string-append
       "In term:~n~v~nThe return type annotation ~a "
       "is ill-formed")
      (unparse-meta-term term)
      (unparse-meta-type B))]
    [('return-type-not-subtype (list term B B^))
     (error 'meta-elaborate
            (string-append
             "In term:~n~v~nThe type of the body ~a should be a "
             "consistent subtype of the declared return type ~a")
            (unparse-meta-term term)
            (unparse-meta-type B^)
            (unparse-meta-type B))]
    [('ill-formed-param-type (list term A))
     (error
        'meta-elaborate
        (string-append
         "In term:~n~v~nThe function parameter type annotation ~a "
         "is ill-formed")
        (unparse-meta-term term)
        (unparse-meta-type A))]
    [('app-arg-not-subtype (list term P-type A))
     (error 'meta-elaborate
            (string-append
             "In term at ~a:~n~v~nThe type of the application argument ~a should be "
             "a consistent subtype of the domain of the type of the function ~a")
            (loc-of term)
            (unparse-meta-term term)
            (unparse-meta-type P-type)
            (unparse-meta-type A))]
    [('invalid-app-fun-type (list term Q-type))
     (error 'meta-elaborate
            (string-append
             "In term:~n~v~nExpected the type of the function in application to "
             "be a function or ?, but got ~a")
            (unparse-meta-term term)
            (unparse-meta-type Q-type))]
    [('ec-param-exists (list α term))
     (error 'meta-elaborate
            (string-append
             "In term:~n~v~nEnvironment classifier parameter ~a is already used "
             "in scope. Use a fresh classifier name.")
            (id->string α) (unparse-meta-term term))]
    [('fail-ecapp-ub (list term ec P-type))
     (error 'meta-elaborate
            (string-append
             "in term:~n~v~nThe env classifier argument ~a should be "
             "a subtype of the upper bound in the universal type ~a")
            (unparse-meta-term term)
            (unparse-ec ec)
            (unparse-meta-type P-type))]
    [('fail-ecapp-lb (list term ec P-type))
     (error 'meta-elaborate
            (string-append
             "in term:~n~v~nThe env classifier argument ~a should be "
             "a supertype of the lower bound in the universal type ~a")
            (unparse-meta-term term)
            (unparse-ec ec)
            (unparse-meta-type P-type))]
    [('invalid-ecapp-type (list term P-type))
     (error 'meta-elaborate
               (string-append
                "In term:~n~v~nExpected the type of the EC abstraction in "
                "EC application to be ∀̇ or ?, but got ~a")
               (unparse-meta-term term)
               (unparse-meta-type P-type))]
    [('ill-formed-static-ec (list term ec ctx))
     (error 'meta-elaborate
            "In term:~n~v~n~a is an ill-formed static EC~nContext:~v"
            (unparse-meta-term term)
            (unparse-ec ec) ctx)]
    [('invalid-set-subtype (list term P-type A))
     (error 'meta-elaborate
            (string-append
             "In term at ~a:~n~v~nThe type of the assignment RHS ~a should be "
             "a subtype of the type stored in the LHS reference ~a")
            (loc-of term)
            (unparse-meta-term term)
            (unparse-meta-type P-type)
            (unparse-meta-type A))]
    [('invalid-set-lhs-type (list term Q-type))
     (error 'meta-elaborate
            (string-append
             "In term:~n~v~nExpected the type of the LHS in "
             "assignment to be ̇Ref or ?, but got ~a")
            (unparse-meta-term term)
            (unparse-meta-type Q-type))]
    [('invalid-deref-type (list term P-type))
     (error 'meta-elaborate
            (string-append
             "In term:~n~v~nExpected the type of the dereference"
             "argument to be ̇Ref or ?, but got ~a")
            (unparse-meta-term term)
            (unparse-meta-type P-type))]
    [('if-test-not-bool (list term A))
     (error 'meta-elaborate
            (string-append
             "In term:~n~v~nThe type of the condition ~a "
             "should be a subtype of type Bool")
            (unparse-meta-term term)
            (unparse-meta-type A))]
    [('bad-let-ann (list binding A A^))
     (error 'meta-elaborate
            (string-append
             "In let* binding at ~a:~n~v~nThe type of the RHS ~a "
             "should be a subtype of type annotation ~a")
            (loc-of binding)
            (unparse-meta-binding binding)
            (unparse-meta-type A^) (unparse-meta-type A))]))

(define (well-formed-meta-type?-log key . args)
  (match* (key args)
    [('ill-formed-ec (list type ec ctx))
     (log debug
             (string-append
              "Code type ~a ill-formed because environment classifier ~a not found "
              "in context ~a")
             (unparse-meta-type type)
             (unparse-ec ec) ctx)]
    [('ec-param-exists (list type α ctx))
     (log debug
             (string-append
              "Universal type ~a ill-formed because environment classifier "
              "parameter ~a already used in context ~a")
             (unparse-meta-type type)
             α ctx)]
    [('ill-formed-static-lb (list type lb ctx))
     (log debug
             (string-append
              "Universal type ~a ill-formed because environment classifier "
              "lower bound ~a is not a well-formed static EC")
             (unparse-meta-type type)
             lb ctx)]
    [('ill-formed-static-ub (list type ub ctx))
     (log debug
             (string-append
              "Universal type ~a ill-formed because environment classifier "
              "upper bound ~a is not a well-formed static EC")
             (unparse-meta-type type)
             ub ctx)]))

(define (handle-code-⋁̃ type1 type2 body-thunk)
  (with-handlers ([(λ (err) (string-prefix? (exn->string err) "ec-⋁"))
                   (λ (err) (meta-type-⋁̃-err 'ec-⋁-fail type1 type2 err))]
                  [(λ (err) (string-prefix? (exn->string err) "object-type-⋁̃"))
                   (λ (err) (meta-type-⋁̃-err 'object-⋁̃-fail type1 type2 err))])
    (body-thunk)))

(define (meta-type-⋁̃-err key . args)
  (match* (key args)
    [('ref-not-same (list type1 type2))
     (error 'meta-type-⋁̃
            "The type arguments of reference types ~a and ~a are not α-equivalent"
            (unparse-meta-type type1)
            (unparse-meta-type type2))]
    [('ec-⋁-fail (list type1 type2 err))
     (error 'meta-type-⋁̃
            (string-append
             "Could not find least upper bound of types ~a and ~a.~nReason:~n~a")
            (unparse-meta-type type1) (unparse-meta-type type2) (exn->string err))]
    [('object-⋁̃-fail (list type1 type2 err))
     (error 'meta-type-⋁̃
            (string-append "Could not find least upper bound of types ~a and ~a.~nReason:~n~a")
            (unparse-meta-type type1) (unparse-meta-type type2) (exn->string err))]
    [('incomparable-types (list type1 type2))
     (error 'meta-type-⋁̃ "Incomparable types for least upper bound:~n~a~n~a~n"
            (unparse-meta-type type1)
            (unparse-meta-type type2))]))

(define (handle-code-⋀̃ type1 type2 body-thunk)
  (with-handlers ([(λ (err) (string-prefix? (exn->string err) "ec-⋀"))
                   (λ (err) (meta-type-⋀̃-err 'ec-⋀-fail type1 type2 err))]
                  [(λ (err) (string-prefix? (exn->string err) "object-type-⋀̃"))
                   (λ (err) (meta-type-⋀̃-err 'object-⋀̃-fail type1 type2 err))])
    (body-thunk)))

(define (meta-type-⋀̃-err key . args)
  (match* (key args)
    [('ref-not-same (list type1 type2))
     (error 'meta-type-⋀̃
            "The type arguments of reference types ~a and ~a are not α-equivalent"
            (unparse-meta-type type1)
            (unparse-meta-type type2))]
    [('ec-⋀-fail (list type1 type2 err))
     (error 'meta-type-⋀̃
            (string-append
             "Could not find greatest lower bound of types ~a and ~a.~nReason:~n~a")
            (unparse-meta-type type1) (unparse-meta-type type2) (exn->string err))]
    [('object-⋀̃-fail (list type1 type2 err))
     (error 'meta-type-⋀̃
            (string-append "Could not find greatest lower bound of types ~a and ~a.~nReason:~n~a")
            (unparse-meta-type type1) (unparse-meta-type type2) (exn->string err))]
    [('incomparable-types (list type1 type2))
     (error 'meta-type-⋀̃ "Incomparable types for greatest lower bound:~n~a~n~a~n"
            (unparse-meta-type type1)
            (unparse-meta-type type2))]))

;; (require racket/trace)
;; (trace meta-elaborate)
;; (trace object-elaborate-check)
;; (trace object-elaborate-synth)
;; (trace coerce-ec)
;; (trace coerce-object)
;; (trace coerce-meta)
;; (trace meta-type-≲)
;; (trace object-type-≲)
;; (trace ec-≲)
