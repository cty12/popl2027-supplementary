#lang racket

(require graph)
(require racket/exn)
(require "logging.rkt")
(require "../utils.rkt")
(require "ast.rkt")
(require "parse.rkt")

(provide (all-defined-out))

(define base-types
  (hasheqv
   'Bool boolean?
   'Int integer?
   'Str string?
   'Unit null?))

(define prim-*-types
  (hasheqv
   'zero? (parse-object-type '(→ Int Bool))
   'sub1 (parse-object-type '(→ Int Int))
   '+ (parse-object-type '(→ Int (→ Int Int)))
   '- (parse-object-type '(→ Int (→ Int Int)))
   '* (parse-object-type '(→ Int (→ Int Int)))
   '/ (parse-object-type '(→ Int (→ Int Int)))
   '% (parse-object-type '(→ Int (→ Int Int)))))

(define prim-meta-types
  prim-*-types)

(define prim-object-types
  prim-*-types)

(struct OType (type ec) #:transparent)
(struct MType (type) #:transparent)
(struct EC () #:transparent)

;; Γ ⊢α Mᵒ : T
;; precondition: (and (object-term? term ctx^)
;;                    (well-formed-ec? ec ctx))
;; where ctx^ is a suitable transformation of ctx to be used by object-term?
(define (object-typecheck-synth ec term [ctx (hash)]
                                [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse term^)
    (object-typecheck-synth ec term^ ctx ec-subtypes))
  (match term
    [(Const k)
     (cond
       [(dict-has-key? prim-object-types k)
        (dict-ref prim-object-types k)]
       [(maybe-base-type k) => (λ (type) type)]
       [else
        (error 'object-typecheck-synth "Undefined object constant: ~a" k)])]
    [(OVar x)
     (unless (dict-has-key? ctx x)
       (error 'object-typecheck-synth "Undefined object variable: ~a" x))
     (match (dict-ref ctx x)
       [(OType T α)
        (unless (ec-<: (ECVar α) ec ec-subtypes)
          (error
           'object-typecheck-synth
           (string-append
            "The environment classifier ~a associated with object variable ~a"
            " was expected to be a subtype of ~a, but it "
            "actually is not.~nContext: ~a~n")
           α x ec ctx))
        T]
       [c (error
           'object-typecheck-synth
           "Object variable ~a expected to be an object type but got ~a.~n"
           x c)])]
    [(OFixAbs α f x S T Mᵒ)
     (when (ec-in-ctx? α ctx)
       (error 'object-typecheck-synth
              (string-append
               "In object fixpoint lambda:~n~v~nEnvironment classifier parameter "
               "is already used in scope. Use a fresh classifier name.")
              (unparse-object-term term)))
     (define T^
       (object-typecheck-synth (ECVar α) Mᵒ
                         (dict-set (dict-set (dict-set ctx α (EC))
                                             x (OType S α))
                                   f (OType (Fun S T) α))
                         (add-subtype ec-subtypes ec (ECVar α))))
     (unless (equal? T^ T)
       (error 'object-typecheck-synth
              (string-append
               "In object fixpoint lambda:~n~v~nThe given return type ~a and actual "
               "type returned ~a are not the same")
              (unparse-object-type T)
              (unparse-object-type T^)))
     (Fun S T^)]
    [(OAbs α x S Mᵒ)
     (when (ec-in-ctx? α ctx)
       (error 'object-typecheck-synth
              (string-append
               "In object lambda:~n~v~nEnvironment classifier parameter "
               "is already used in scope. Use a fresh classifier name.")
              (unparse-object-term term)))
     (define T^
       (object-typecheck-synth (ECVar α) Mᵒ
                         (dict-set (dict-set ctx α (EC))
                                   x (OType S α))
                         (add-subtype ec-subtypes ec (ECVar α))))
     (Fun S T^)]
    [(App Lᵒ Mᵒ)
     (match (recurse Lᵒ)
       [(Fun S T)
        (object-typecheck-check ec Mᵒ S ctx ec-subtypes)
        T]
       [fun-type
        (error 'object-typecheck-synth
               (string-append
                "Type of the function in application\n\t~a\n"
                "should be a function, but found:\n\t~a")
               (unparse-object-term term)
               (unparse-object-type fun-type))])]
    [(If Lᵒ Mᵒ Nᵒ)
     (object-typecheck-check ec Lᵒ (Base 'Bool) ctx ec-subtypes)
     (define then-type (recurse Mᵒ))
     (define else-type (recurse Nᵒ))
     (unless (equal? then-type else-type)
       (error 'object-typecheck-synth
              (string-append
               "Type of the then term ~a and else term ~a in ~a should "
               "be the same")
              (unparse-object-type then-type)
              (unparse-object-type else-type)
              (unparse-object-term term)))
     then-type]
    [(Asc Mᵒ T)
     (object-typecheck-check ec Mᵒ T ctx ec-subtypes)
     T]
    [(Splice _)
     (error 'object-typecheck-synth
            (string-append
             "In term:~n~v~nCannot synthesize a type for splice term. "
             "Try ascribing a type to the term")
            (unparse-object-term term))]
    [_ (error 'object-typecheck-synth "Cannot handle term:~n~v~n" term)]))

(define (object-typecheck-check ec term type [ctx (hash)]
                                [ec-subtypes (unweighted-graph/directed '())])
  (match term
    [(Splice M)
     (define A (meta-typecheck M ctx ec-subtypes))
     (define B (Code type ec))
     (unless (meta-type-<: A B ctx ec-subtypes)
       (error 'object-typecheck-check
              (string-append
               "In term:~n~v~nThe type of the spliced term ~a should be a "
               "subtype of ~a" "~nwith subtypes~n~a")
              (unparse-object-term term)
              (unparse-meta-type A)
              (unparse-meta-type B)
              (get-edges ec-subtypes)))]
    [term
     (define T (object-typecheck-synth ec term ctx ec-subtypes))
     (unless (equal? T type)
       (error 'object-typecheck-check
              "In:~n~v~n checked type ~a is not equal to synthesized type ~a"
              (unparse-object-term term) (unparse-object-type type)
              (unparse-object-type T)))]
    [_ (error 'object-typecheck-check "Cannot handle term:~n~v~n" term)]))

;; Γ ⊢ M : A
;; precondition: (meta-term? term ctx^)
;; where ctx^ is a suitable transformation of ctx to be used by meta-term?
(define (meta-typecheck term [ctx (hash)]
                        [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse term^)
    (meta-typecheck term^ ctx  ec-subtypes))
  (match term
    [(Const k)
     (cond
       [(dict-has-key? prim-meta-types k)
        (dict-ref prim-meta-types k)]
       [(maybe-base-type k) => (λ (type) type)]
       [else
        (error 'meta-typecheck "Undefined meta constant: ~a" k)])]
    [(MVar x)
     (unless (dict-has-key? ctx x)
       (error 'meta-typecheck "Undefined meta variable: ~a" x))
     (match (dict-ref ctx x)
       [(MType A) A]
       [c (error
           'meta-typecheck
           "Meta variable ~a expected to be a meta type but got ~a.~n"
           x c)])]
    [(MFixAbs f x A B M)
     (unless (well-formed-meta-type? A ctx)
       (error
        'meta-typecheck
        (string-append
         "In meta fixpoint lambda:~n~v~nThe function parameter type annotation ~a "
         "is ill-formed")
        (unparse-meta-term term)
        (unparse-meta-type A)))
     (unless (well-formed-meta-type? B ctx)
       (error
        'meta-typecheck
        (string-append
         "In meta fixpoint lambda:~n~v~nThe return type annotation ~a "
         "is ill-formed")
        (unparse-meta-term term)
        (unparse-meta-type B)))
     (define B^
       (meta-typecheck M
                       (dict-set (dict-set ctx x (MType A))
                                 f (MType (Fun A B)))
                       ec-subtypes))
     (unless (meta-type-<: B^ B)
       (error 'meta-elaborate
              (string-append
               "In term:~n~v~nThe type of the body ~a should be a "
               "consistent subtype of the declared return type ~a")
              (unparse-meta-term term)
              (unparse-meta-type B^)
              (unparse-meta-type B)))
     (Fun A B)]
    [(MAbs x A M)
     (unless (well-formed-meta-type? A ctx)
       (error
        'meta-typecheck
        (string-append
         "In meta lambda:~n~v~nThe function parameter type annotation ~a "
         "is ill-formed")
        (unparse-meta-type A)
        (unparse-meta-term term)))
     (define B^
       (meta-typecheck M (dict-set ctx x (MType A)) ec-subtypes))
     (Fun A B^)]
    [(App L M)
     (match (recurse L)
       [(Fun A B)
        (define arg-type (recurse M))
        (unless (meta-type-<: arg-type A ctx ec-subtypes)
          (error 'meta-typecheck
                 (string-append
                  "In function application:\n\t~a\nthe type of the argument\n\t"
                  "~a\nshould be a subtype of the input type of the function\n\t"
                  "~a\nbut it isn't")
                 (unparse-meta-term term)
                 (unparse-meta-type arg-type)
                 (unparse-meta-type A)))
        B]
       [fun-type
        (error 'meta-typecheck
               (string-append
                "Type of the function in function application ~a should "
                "be a function, but found: ~a")
               (unparse-meta-term term)
               (unparse-meta-type fun-type))])]
    [(ECAbs α lb ub M)
     (unless (if lb (well-formed-ec? lb ctx) #t)
       (error 'meta-typecheck
              "Environment classifier lower bound ~a used in ~a is undefined"
              (unparse-ec lb) (unparse-meta-term term)))
     (unless (if ub (well-formed-ec? ub ctx) #t)
       (error 'meta-typecheck
              "Environment classifier upper bound ~a used in ~a is undefined"
              (unparse-ec ub) (unparse-meta-term term)))
     (when (ec-in-ctx? α ctx)
       (error 'meta-typecheck
              (string-append
               "Environment classifier parameter of ~a is already used in scope. "
               "Use a fresh classifier name.")
              (unparse-meta-term term)))
     (define B
       (meta-typecheck M (dict-set ctx α (EC))
                       (add-subtype (add-subtype ec-subtypes (ECVar α) ub)
                                    lb (ECVar α))))
     (ECUniv α lb ub B)]
    [(ECApp M ec1)
     (unless (well-formed-ec? ec1 ctx)
       (error 'meta-typecheck
              "Environment classifier ~a used in ~a is undefined"
              (unparse-ec ec1)
              (unparse-meta-term term)))
     (match (recurse M)
       [(and (ECUniv β lb ub A) univ-type)
        (unless (if ub (ec-<: ec1 ub ec-subtypes) #t)
          (error 'meta-typecheck
               (string-append
                "The env classifier argument ~a in the term ~a should be "
                "a subtype of the upper bound in the universal type ~a")
               (unparse-ec ec1)
               (unparse-meta-term term)
               (unparse-meta-type univ-type)))
        (unless (if lb (ec-<: lb ec1 ec-subtypes) #t)
          (error 'meta-typecheck
                 (string-append
                  "The env classifier argument ~a in the term ~a should be "
                  "a supertype of the lower bound in the universal type ~a")
                 (unparse-ec ec1)
                 (unparse-meta-term term)
                 (unparse-meta-type univ-type)))
        (type-ec-rename A β ec1)]
       [type
        (error 'meta-typecheck
               (string-append
                "Type of the term in environment classifier application "
                "~a should be an environment classifier universal type, "
                "but found: ~a")
               (unparse-meta-term term)
               (unparse-meta-type type))])]
    [(Quote Mᵒ ec)
     (unless (well-formed-ec? ec ctx)
       (error 'meta-typecheck
              "Environment classifier ~a used in ~a is undefined"
              (unparse-ec ec)
              (unparse-meta-term term)))
     (Code (object-typecheck-synth ec Mᵒ ctx ec-subtypes) ec)]
    [(Ref M)
     (RefT (recurse M))]
    [(Set L M)
     (match (recurse L)
       [(RefT A)
        (define rhs-type (recurse M))
        (unless (meta-type-<: rhs-type A ctx ec-subtypes)
          (error 'meta-typecheck
                 (string-append
                  "In refence assignment ~a, the type stored in the "
                  "reference ~a should be a supertype of the RHS type "
                  "~a but it isn't")
                 (unparse-meta-term term)
                 (unparse-meta-type A)
                 (unparse-meta-type rhs-type)))
        (Base 'Unit)]
       [ref-type
        (error 'meta-typecheck
               (string-append
                "Type of the LHS in reference assignment ~a should "
                "be a reference, but found: ~a")
               (unparse-meta-term term)
               (unparse-meta-type ref-type))])]
    [(Deref M)
     (match (recurse M)
       [(RefT A) A]
       [deref-type
        (error 'meta-typecheck
               (string-append
                "Type of the term being dereferenced in ~a should "
                "be a reference, but found: ~a")
               (unparse-meta-term term)
               (unparse-meta-type deref-type))])]
    [(If L M N)
     (match (recurse L)
       [(Base 'Bool)
        (define then-type (recurse M))
        (define else-type (recurse N))
        (meta-type-⨆ then-type else-type ctx ec-subtypes)]
       [cond-type
        (error 'meta-typecheck
               (string-append
                "Type of the condition term in ~a should "
                "be boolean, but found: ~a")
               (unparse-meta-term term)
               (unparse-meta-type cond-type))])]))

(define (ec-in-ctx? α ctx)
  (and (dict-has-key? ctx α) (EC? (dict-ref ctx α))))

;; Γ ⊢ α
(define (well-formed-ec? ec ctx)
  (match ec
    [(ECEps) #t]
    [(ECVar α) 
     (ec-in-ctx? α ctx)]
    [else #f]))

;; Γ ⊢ A
(define (well-formed-meta-type? type [ctx (hash)])
  (match type
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
       [(well-formed-ec? ec ctx)
        #t]
       [else
        (log debug
             (string-append
              "Code type ~a ill-formed because environment classifier ~a not found "
              "in context ~a")
             (unparse-meta-type type)
             (unparse-ec ec) ctx)
        #f])]
    [(ECUniv α lb ub A)
     ;; wf-univ
     (cond
       [(ec-in-ctx? α ctx)
        (log debug
             (string-append
              "Universal type ~a ill-formed because environment classifier "
              "parameter ~a already used in context ~a")
             (unparse-meta-type type)
             α ctx)
        #f]
       [(not (if ub (well-formed-ec? ub ctx) #t))
        (log debug
             (string-append
              "Universal type ~a ill-formed because environment classifier "
              "upper bound ~a not found in context ~a")
             (unparse-meta-type type)
             (unparse-ec ub) ctx)
        #f]
       [(not (if lb (well-formed-ec? lb ctx) #t))
        (log debug
             (string-append
              "Universal type ~a ill-formed because environment classifier "
              "lower bound ~a not found in context ~a")
             (unparse-meta-type type)
             lb ctx)
        #f]
       [else (well-formed-meta-type? A (dict-set ctx α (EC)))])]
    [_ (error 'well-formed-meta-type? "Invalid meta type: ~a" type)]))

(define (maybe-base-type k)
  (for/or ([(type pred?) (in-dict base-types)])
    (cond
      [(pred? k) (Base type)]
      [else #f])))

;; Γ ⊢ α <: β
;; precondition: ∃ ctx,
;;               (and (well-formed-ec? ec1 ctx)
;;                    (well-formed-ec? ec2 ctx))
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

;; Γ ⊢ A <: B
;; precondition: (and (well-formed-meta-type? type1 ctx)
;;                    (well-formed-meta-type? type2 ctx))
(define (meta-type-<: type1 type2 [ctx (hash)]
                      [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse-<: A B)
    (meta-type-<: A B ctx ec-subtypes))
  (match* (type1 type2)
    [((Base ι) (Base ι^)) #:when (equal? ι ι^) #t]
    [((Fun A B) (Fun A^ B^))
     (and (recurse-<: A^ A) (recurse-<: B B^))]
    [((RefT A) (RefT B))
     (cond
       [(not (meta-type-<: A B ec-subtypes))
        (log debug
             "~a should be a subtype of ~a"
             (unparse-meta-type type1)
             (unparse-meta-type type2))
        #f]
       [(not (meta-type-<: B A ec-subtypes))
        (log debug
             "~a should be a subtype of ~a"
             (unparse-meta-type type2)
             (unparse-meta-type type1))
        #f]
       [else #t])]
    [((Code T ec1) (Code T^ ec2))
     #:when (equal? T T^)
     (cond
       [(not (ec-<: ec1 ec2 ec-subtypes))
        (log debug
             "The env classifier used in code type ~a is not a subtype of the one used in the code type ~a"
             (unparse-meta-type type1)
             (unparse-meta-type type2))
        #f]
       [else #t])]
    [((ECUniv α lb ub A) (ECUniv β lb^ ub^ B))
     #:when (and (equal? ub ub^) (equal? lb lb^))
     (define α^ (gen-id 'α))
     (define ec-α^ (ECVar α^))
     (meta-type-<: (type-ec-rename A α ec-α^)
                   (type-ec-rename B β ec-α^)
                   (dict-set ctx α^ (EC))
                   (add-subtype (add-subtype ec-subtypes ec-α^ ub) lb ec-α^))]
    [(_ _)
     (log debug "Incomparable types for subtype check:~n~a~n~a~n"
          (unparse-meta-type type1)
          (unparse-meta-type type2))
     #f]))


(define (ecs-in-ctx ctx)
  (for/list ([(k v) (in-dict ctx)]
             #:when (EC? v))
    (ECVar k)))

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

;; Γ ⊢ α ⨆ β = γ
;; precondition: ∃ ctx,
;;               (and (well-formed-ec? ec1 ctx)
;;                    (well-formed-ec? ec2 ctx))
(define (ec-⨆ ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [(_ (ECEps))
     ec1]
    [((ECEps) _)
     ec2]
    [((ECVar α) (ECVar β)) #:when (equal? α β)
     (ECVar α)]
    [((ECVar α) (ECVar β))
     ;; ec-⨆-traverse
     (define ⨆ (graph-⨆ α β ec-subtypes))
     (match (length ⨆)
       [0 (error 'ec-⨆
                 (string-append
                  "No least upper bound found for ~a and ~a."
                  "~nSubtypes: ~a")
                 ec1 ec2 (get-edges ec-subtypes))]
       [1 (ECVar (car ⨆))]
       [_ (error 'ec-⨆
                 (string-append
                  "Multiple least upper bounds found for ~a and ~a."
                  "~nLUB candidates: ~a~nSubtypes: ~a")
                 α β ⨆ (get-edges ec-subtypes))])]))

;; Γ ⊢ α ⨅ β = γ
;; precondition: ∃ ctx,
;;               (and (well-formed-ec? ec1 ctx)
;;                    (well-formed-ec? ec2 ctx))
(define (ec-⨅ ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [((ECEps) _)
     (ECEps)]
    [(_ (ECEps))
     (ECEps)]
    [((ECVar α) (ECVar β)) #:when (equal? α β)
     ;; ec-⨅-self
     (ECVar α)]
    [((ECVar α) (ECVar β))
     ;; ec-⨅-traverse
     (define ⨅ (graph-⨆ α β (transpose ec-subtypes)))
     (match (length ⨅)
       [0 (ECEps)]
       [1 (ECVar (car ⨅))]
       [_ (error 'ec-⨅
                 (string-append
                  "Multiple greatest lower bounds found for ~a and ~a."
                  "~nGLB candidates: ~a~nSubtypes: ~a")
                 α β ⨅ (get-edges ec-subtypes))])]))

(define (graph-⨆ α β ec-subtypes)
  (define-values (distanceα _1) (bfs ec-subtypes α))
  (define-values (distanceβ _2) (bfs ec-subtypes β))
  (define supertypesα
    (for/set ([(u d) (in-dict distanceα)]
              #:when (not (infinite? d)))
      u))
  (define supertypesβ
    (for/set ([(u d) (in-dict distanceβ)]
              #:when (not (infinite? d)))
      u))
  (define upper-bounds (set-intersect supertypesα supertypesβ))
  (define ub-in-degrees
    (for*/fold ([in-deg (for/hash ([k (in-set upper-bounds)])
                          (values k 0))])
               ([ub (in-set upper-bounds)]
                [n (in-neighbors ec-subtypes ub)]
                #:when (set-member? upper-bounds n))
      (dict-set in-deg n (add1 (dict-ref in-deg n)))))
  ;; This will fail to find a least upper bound if there is a loop in
  ;; ec-subtypes (maybe a TODO?)
  (for/list ([(k v) (in-dict ub-in-degrees)]
             #:when (zero? v))
    k))

;; Γ ⊢ A ⨆ B = C
;; precondition: (and (well-formed-meta-type? type1 ctx)
;;                    (well-formed-meta-type? type2 ctx))
(define (meta-type-⨆ type1 type2 [ctx (hash)]
                      [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse-⨆ A B) (meta-type-⨆ A B ctx ec-subtypes))
  (match* (type1 type2)
    [((Base ι) (Base ι^)) #:when (equal? ι ι^) (Base ι)]
    [((Fun A B) (Fun A^ B^))
     (Fun (meta-type-⨅ A^ A ctx ec-subtypes) (recurse-⨆ B B^))]
    [((RefT A) (RefT B))
     (define ecs (ecs-in-ctx ctx))
     (unless (meta-type-α-equiv? A B ecs ecs)
       (error 'meta-type-⨆
              "The type arguments of reference types ~a and ~a are not α-equivalent"
              (unparse-meta-type type1)
              (unparse-meta-type type2)))
     (RefT A)]
    [((Code T ec1) (Code T^ ec2))
     #:when (equal? T T^)
     (with-handlers ([(λ (e) (string-prefix? (exn->string e) "ec-⨆"))
                      (λ (e) (error 'meta-type-⨆
                                    (string-append
                                     "Could not find least upper bound of types "
                                     "~a and ~a.~nReason:~n~a")
                                    (unparse-meta-type type1)
                                    (unparse-meta-type type2)
                                    (exn->string e)))])
       (Code T (ec-⨆ ec1 ec2 ec-subtypes)))]
    [((ECUniv α lb ub A) (ECUniv β lb^ ub^ B))
     #:when (equal? lb lb^) (equal? ub ub^)
     (define α^ (gen-id 'α))
     (define ec-α^ (ECVar α^))
     (ECUniv α^ lb ub
             (meta-type-⨆ (type-ec-rename A α ec-α^)
                          (type-ec-rename B β ec-α^)
                          (dict-set ctx α^ (EC))
                          (add-subtype (add-subtype ec-subtypes lb ec-α^) ec-α^ ub)))]
    [(_ _)
     (error 'meta-type-⨆ "Incomparable types for least upper bound:~n~a~n~a~n"
            (unparse-meta-type type1)
            (unparse-meta-type type2))]))

;; Γ ⊢ A ⨅ B = C
;; precondition: (and (well-formed-meta-type? type1 ctx)
;;                    (well-formed-meta-type? type2 ctx))
(define (meta-type-⨅ type1 type2 [ctx (hash)]
                     [ec-subtypes (unweighted-graph/directed '())])
  (define (recurse-⨅ A B)
    (meta-type-⨅ A B ctx ec-subtypes))
  (match* (type1 type2)
    [((Base ι) (Base ι^)) #:when (equal? ι ι^) (Base ι)]
    [((Fun A B) (Fun A^ B^))
     (Fun (meta-type-⨆ A^ A ctx ec-subtypes) (recurse-⨅ B B^))]
    [((RefT A) (RefT B))
     (define ecs (ecs-in-ctx ctx))
     (unless (meta-type-α-equiv? A B ecs ecs)
       (error 'meta-type-⨅
              "The type arguments of reference types ~a and ~a are not α-equivalent"
              (unparse-meta-type type1)
              (unparse-meta-type type2)))
     (RefT A)]
    [((Code T ec1) (Code T^ ec2))
     #:when (equal? T T^)
     (with-handlers ([(λ (e) (string-prefix? (exn->string e) "ec-⨅"))
                      (λ (e) (error 'meta-type-⨅
                                    (string-append
                                     "Could not find greatest lower bound of types "
                                     "~a and ~a.~nReason:~n~a")
                                    (unparse-meta-type type1)
                                    (unparse-meta-type type2)
                                    (exn->string e)))])
       (Code T (ec-⨅ ec1 ec2 ec-subtypes)))]
    [((ECUniv α lb ub A) (ECUniv β lb^ ub^ B))
     #:when (and (equal? lb lb^) (equal? ub ub^))
     (define α^ (gen-id 'α))
     (ECUniv α^ lb^ ub^
             (meta-type-⨅ (type-ec-rename A α (ECVar α^))
                   (type-ec-rename B β (ECVar α^))
                   (dict-set ctx α^ (EC))
                   (add-subtype (add-subtype ec-subtypes lb^ (ECVar α^))
                                (ECVar α^) ub^)))]
    [(_ _)
     (error 'meta-type-⨅ "Incomparable types for greatest lower bound:~n~a~n~a~n"
          (unparse-meta-type type1)
          (unparse-meta-type type2))]))
