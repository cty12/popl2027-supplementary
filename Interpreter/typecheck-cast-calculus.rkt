#lang racket

;; This file is to ensure that elaboration into the coercion calculus preserves
;; the type of the original term

(require graph)
(require "ast.rkt")
(require (only-in "parse.rkt"
                  unparse-meta-type unparse-object-type
                  unparse-meta-term unparse-object-term
                  unparse-meta-hypercoercion unparse-object-hypercoercion
                  unparse-meta-hc-head unparse-obj-hc-head
                  unparse-meta-hc-middle unparse-obj-hc-middle
                  unparse-meta-hc-tail unparse-obj-hc-tail
                  unparse-ec-hypercoercion unparse-ec-hc-middle unparse-ec))
(require (rename-in (only-in "typecheck.rkt"
                             ec-var-in-ctx? ec-<: well-formed-meta-type?-log
                             well-formed-static-ec? ground-type? well-formed-ec?
                             prim-types base-types maybe-base-type
                             add-subtype Prim->type)
                    (ec-<: ec-<:^)))
(require (only-in "sister-language/typecheck.rkt"
                  EC MType OType
                  ecs-in-ctx))

(provide (all-defined-out))

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
    [(ECUnivCC α A)
     ;; wf-univ
     (cond
       [(ec-var-in-ctx? α ctx)
        (well-formed-meta-type?-log 'ec-param-exists type α ctx)
        #f]
       [else (well-formed-meta-type? A (dict-set ctx α (EC)))])]
    [(ECSub sub-ec sup-ec A)
     (cond
       [(not (well-formed-static-ec? sub-ec ctx))
        (well-formed-meta-type?-log 'ill-formed-ec type sub-ec ctx)
        #f]
       [(not (well-formed-static-ec? sup-ec ctx))
        (well-formed-meta-type?-log 'ill-formed-ec type sup-ec ctx)
        #f]
       [else (well-formed-meta-type? A ctx)])]    
    [_ (error 'well-formed-meta-type? "Invalid meta type: ~a" type)]))

(define (object-cc-typecheck ec term Γ θ Σ)
  (define (recurse term^)
    (object-cc-typecheck ec term^ Γ θ Σ))
  (match term
    [(Const k)
     (cond
       [(dict-has-key? prim-types k)
        (dict-ref prim-types k)]
       [(maybe-base-type k) => (λ (type) type)]
       [else (error 'object-cc-typecheck "Undefined object constant: ~a" k)])]
    [(OVar x)
     (unless (dict-has-key? Γ x) (error 'object-cc-typecheck "Undefined object variable: ~a" x))
     (match (dict-ref Γ x)
       [(OType T α)
        (unless (ec-<: (ECVar α) ec θ) (object-cc-typecheck-err 'ovar-not-subtype α x ec θ))
        T]
       [c (error 'object-cc-typecheck "Object variable ~a expected to be an object type but got ~a.~n" x c)])]
    [(OFixAbs α f β x S T Mᵒ)
     (when (ec-var-in-ctx? α Γ) (object-cc-typecheck-err 'ec-exists term))
     (define Γ^ (dict-set (dict-set Γ α (EC)) f (OType (Fun S T) α)))
     (define Γ^^ (dict-set (dict-set Γ^ β (EC)) x (OType S β)))
     (define Θ^ (add-subtype (add-subtype θ ec (ECVar α)) (ECVar α) (ECVar β)))
     (define T^ (object-cc-typecheck (ECVar β) Mᵒ Γ^^ Θ^ Σ))
     (unless (equal? T^ T) (object-cc-typecheck-err 'ofixabs-return-type-mismatch T T^))
     (Fun S T)]
    [(OFixAbsVal α f β x S T Mᵒ)
     (define T^ (object-cc-typecheck (ECVar β) Mᵒ Γ θ Σ))
     (unless (equal? T^ T) (object-cc-typecheck-err 'ofixabs-return-type-mismatch T T^))
     (Fun S T)]
    [(AppAnn Lᵒ Mᵒ T^)
     (define func-type (recurse Lᵒ))
     (match func-type
       [(Fun S T)
        (define arg-type (recurse Mᵒ))
        (unless (equal? arg-type S) (object-cc-typecheck-err 'wrong-arg-type term S arg-type))
        T]
       [fun-type (object-cc-typecheck-err 'wrong-fun-type term fun-type)])]
    [(IfAnn Lᵒ Mᵒ Nᵒ T)
     (define test-type (recurse Lᵒ))
     (unless (equal? test-type (Base 'Bool)) (object-cc-typecheck-err 'if-test-not-bool term test-type))
     (define then-type (recurse Mᵒ))
     (define else-type (recurse Nᵒ))
     (unless (equal? then-type else-type) (object-cc-typecheck-err 'wrong-if-branches term then-type else-type))
     (unless (equal? then-type T) (object-cc-typecheck-err 'wrong-if-ann term then-type T))
     then-type]
    [(Splice P)
     (define S (meta-cc-typecheck P Γ θ Σ))
     (unless (Code? S) (object-cc-typecheck-err 'wrong-splice-type term S))
     (define ec^ (Code-ec S))
     (unless (equal? ec^ ec) (object-cc-typecheck-err 'wrong-splice-ec term ec ec^))
     (Code-type S)]
    [(Blame T ℓ) T]
    [_ (error 'object-cc-typecheck "Cannot handle term:~n~v~n" term)]))

(define (meta-cc-typecheck term [Γ (hash)]
                           [θ (unweighted-graph/directed '())]
                           [Σ (vector)])
  (define (recurse term^) (meta-cc-typecheck term^ Γ θ Σ))
  (match term
    [(Const k)
     (cond
       [(dict-has-key? prim-types k)
        (dict-ref prim-types k)]
       [(maybe-base-type k) => (λ (type) type)]
       [else (error 'meta-cc-typecheck "Undefined meta constant: ~a" k)])]
    [(MVar x)
     (unless (dict-has-key? Γ x) (error 'meta-cc-typecheck "Undefined meta variable: ~a" x))
     (match (dict-ref Γ x)
       [(MType A) A]
       [c (error 'meta-cc-typecheck "Meta variable ~a expected to be of meta type but got ~a.~n" x c)])]
    [(MFixAbs f x A B P)
     (unless (well-formed-meta-type? A Γ) (meta-cc-typecheck-err 'ill-formed-param-type term A))
     (unless (well-formed-meta-type? B Γ) (meta-cc-typecheck-err 'ill-formed-return-type term B))
     (define Γ^ (dict-set (dict-set Γ x (MType A)) f (MType (Fun A B))))
     (define B^ (meta-cc-typecheck P Γ^ θ Σ))
     (unless (meta-type-α-equiv? B^ B) (meta-cc-typecheck-err 'mismatched-return-type term B^ B))
     (Fun A B)]
    [(MAbs x A P)
     (unless (well-formed-meta-type? A Γ) (meta-cc-typecheck-err 'ill-formed-param-type term A))
     (define B (meta-cc-typecheck P (dict-set Γ x (MType A)) θ Σ))
     (Fun A B)]
    [(App Q P)
     (define Q-type (recurse Q))
     (define P-type (recurse P))
     (match Q-type
       [(Fun A₁ A₂)
        (unless (meta-type-α-equiv? P-type A₁) (meta-cc-typecheck-err 'wrong-arg-type term P-type A₁))
        A₂]
       [_ (meta-cc-typecheck-err 'wrong-fun-type term Q-type)])]
    [(ECAbsCC α P)
     (when (ec-var-in-ctx? α Γ) (meta-cc-typecheck-err 'ec-param-exists term))
     (define P-type (meta-cc-typecheck P (dict-set Γ α (EC)) θ Σ))
     (ECUnivCC α P-type)]
    [(ECApp P ec)
     (unless (well-formed-static-ec? ec Γ) (meta-cc-typecheck-err 'ill-formed-static-ec term ec))
     (define P-type (recurse P))
     (match P-type
       [(ECUnivCC β A)
        (type-ec-rename A β ec)]
       [_ (meta-cc-typecheck-err 'wrong-ecapp-type term P-type)])]
    [(ECSubIntro sub-ec sup-ec P)
     (unless (well-formed-static-ec? sub-ec Γ) (meta-cc-typecheck-err 'ill-formed-static-ec term sub-ec))
     (unless (well-formed-static-ec? sup-ec Γ) (meta-cc-typecheck-err 'ill-formed-static-ec term sup-ec))
     (define P-type (meta-cc-typecheck P Γ (add-subtype θ sub-ec sup-ec) Σ))
     (ECSub sub-ec sup-ec P-type)]
    [(ECSubElim P)
     (define P-type (meta-cc-typecheck P Γ θ Σ))
     (match P-type
       [(ECSub sub-ec sup-ec A)
        (unless (ec-<: sub-ec sup-ec θ) (meta-cc-typecheck-err 'sub-elim-sub-fail term sub-ec sup-ec))
        A]
       [else (meta-cc-typecheck-err 'sub-elim-bad-type term P-type)])]
    [(ECSubElimDyn P ℓ)
     (define P-type (meta-cc-typecheck P Γ θ Σ))
     (match P-type
       [(Dyn)
        (Dyn)]
       [else
        (error 'meta-cc-typecheck "in sub-elim-dyn, expected ⋆, not ~a" (unparse-meta-type P-type))])]
    [(Quote Pᵒ ec)
     (unless (well-formed-static-ec? ec Γ) (meta-cc-typecheck-err 'ill-formed-static-ec term ec))
     (define T (object-cc-typecheck ec Pᵒ Γ θ Σ))
     (Code T ec)]
    [(RefAnn P A)
     (define A^ (recurse P))
     (unless (meta-type-α-equiv? A A^) (meta-cc-typecheck-err 'ref-mismatched-ann term A A^))
     (RefT A)]
    [(Set Q P)
     (define Q-type (recurse Q))
     (define P-type (recurse P))
     (match Q-type
       [(RefT A)
        (unless (meta-type-α-equiv? P-type A) (meta-cc-typecheck-err 'set-types-mismatch term P-type A))
        (Base 'Unit)]
       [_ (meta-cc-typecheck-err 'wrong-set-lhs term Q-type)])]
    [(Deref P)
     (define P-type (recurse P))
     (match P-type
       [(RefT A) A]
       [_ (meta-cc-typecheck-err 'wrong-deref-type term P-type)])]
    [(IfAnn Q P R B)
     (define A (recurse Q))
     (unless (equal? A (Base 'Bool)) (meta-cc-typecheck-err 'if-test-not-bool term A))
     (define B₁ (recurse P))
     (define B₂ (recurse R))
     (unless (meta-type-α-equiv? B₁ B₂) (meta-cc-typecheck-err 'wrong-if-branches term B₁ B₂))
     (unless (meta-type-α-equiv? B₁ B) (meta-cc-typecheck-err 'wrong-if-ann term B₁ B))
     B₁]
    [(Cast P C)
     (define A (recurse P))
     (define-values (src tgt) (meta-hypercoercion-typecheck C Γ θ))
     (unless (meta-type-α-equiv? src A) (meta-cc-typecheck-err 'cast-coerc-mismatch term A src))
     tgt]
    [(Blame A ℓ)
     (unless (well-formed-meta-type? A Γ) (meta-cc-typecheck-err 'ill-formed-blame-ann term A))
     A]
    [(Loc addr)
     (define heap-size (vector-length Σ))
     (unless (< addr heap-size) (meta-cc-typecheck-err 'loc-out-of-bounds addr heap-size))
     (RefT (vector-ref Σ addr))]
    [(Prim args-t ret-t _ name) (Prim->type args-t ret-t name)]
    [_ (error 'meta-cc-typecheck "Cannot handle term:~n~v~n" term)]))

(define (ec-<: ec1 ec2 ec-subtypes)
  (match* (ec1 ec2)
    [((Dyn) (Dyn)) #t]
    [(_ _) (ec-<:^ ec1 ec2 ec-subtypes)]))

(define (meta-hypercoercion-typecheck hc ctx ec-subtypes)
  (match hc
    [(CHyp h m t)
     (define-values (hd-src hd-tgt) (meta-hc-head-typecheck h ctx))
     (define-values (md-src md-tgt) (meta-hc-middle-typecheck m ctx ec-subtypes))
     (define-values (tl-src tl-tgt) (meta-hc-tail-typecheck t ctx))
     (unless (meta-type-α-equiv? hd-tgt md-src) (hc-typecheck-err "meta" 'head-middle hc hd-tgt md-src))
     (unless (meta-type-α-equiv? md-tgt tl-src) (hc-typecheck-err "meta" 'middle-tail hc md-tgt tl-src))
     (values hd-src tl-tgt)]))

(define (meta-hc-head-typecheck h ctx)
  (match h
    [(CProj G ℓ)
     (unless (and (ground-type? G) (well-formed-meta-type? G ctx)) (meta-hc-hd-typecheck-err 'bad-proj h G))
     (values (Dyn) G)]
    [(CId A)
     (unless (well-formed-meta-type? A ctx) (meta-hc-hd-typecheck-err 'bad-id h A))
     (values A A)]
    [_ (error 'meta-hc-head-typecheck "Invalid meta hypercoercion head: ~a" h)]))

(define (meta-hc-middle-typecheck m ctx ec-subtypes)
  (define (recurse C) (meta-hypercoercion-typecheck C ctx ec-subtypes))
  (match m
    [(CFun C₁ C₂)
     (define-values (A₂ A₁) (recurse C₁))
     (define-values (B₁ B₂) (recurse C₂))
     (values (Fun A₁ B₁) (Fun A₂ B₂))]
    [(CCode Cᵒ Cᵉ)
     (define-values (O₁ O₂) (object-hypercoercion-typecheck Cᵒ))
     (define-values (ê ê^) (ec-hypercoercion-typecheck Cᵉ ctx ec-subtypes))
     (values (Code O₁ ê) (Code O₂ ê^))]
    [(CRefT write-coer read-coer)
     (define-values (B A) (recurse write-coer))
     (define-values (A^ B^) (recurse read-coer))
     (unless (meta-type-α-equiv? A A^) (meta-hc-md-typecheck-err 'write-tgt-mismatch m A A^))
     (unless (meta-type-α-equiv? B B^) (meta-hc-md-typecheck-err 'write-src-mismatch m B B^))
     (values (RefT A) (RefT B))]
    [(CECUniv α C)
     (when (ec-var-in-ctx? α ctx) (meta-hc-md-typecheck-err 'ec-param-exists m))
     (define-values (A B)
       (meta-hypercoercion-typecheck C (dict-set ctx α (EC)) ec-subtypes))
     (values (ECUnivCC α A) (ECUnivCC α B))]
    [(CECSub sub-ec sup-ec C)
     (unless (well-formed-static-ec? sub-ec ctx) (meta-hc-md-typecheck-err 'invalid-sub-ec m sub-ec))
     (unless (well-formed-static-ec? sup-ec ctx) (meta-hc-md-typecheck-err 'invalid-sup-ec m sup-ec))
     (define ec-subtypes^ (add-subtype ec-subtypes sub-ec sup-ec))
     (define-values (A B) (meta-hypercoercion-typecheck C ctx ec-subtypes^))
     (values (ECSub sub-ec sup-ec A) (ECSub sub-ec sup-ec B))]
    [(CId (Dyn)) (values (Dyn) (Dyn))]
    [(CId (and base (Base ι)))
     (unless (dict-has-key? base-types ι) (meta-hc-md-typecheck-err 'bad-id-base m ι))
     (values base base)]
    [(CBot A B ℓ)
     (unless (well-formed-meta-type? A ctx) (meta-hc-md-typecheck-err 'bad-bot-src m A))
     (unless (well-formed-meta-type? B ctx) (meta-hc-md-typecheck-err 'bad-bot-tgt m B))
     (values A B)]
    [_ (error 'meta-hc-middle-typecheck "Invalid meta hypercoercion middle: ~a" m)]))

(define (meta-hc-tail-typecheck t ctx)
  (match t
    [(CInj G)
     (unless (and (ground-type? G) (well-formed-meta-type? G ctx)) (meta-hc-tl-typecheck-err 'bad-inj t G))
     (values G (Dyn))]
    [(CId A)
     (unless (well-formed-meta-type? A ctx) (meta-hc-tl-typecheck-err 'bad-id t A))
     (values A A)]
    [_ (error 'meta-hc-tail-typecheck "Invalid meta hypercoercion tail: ~a" t)]))

(define (object-hypercoercion-typecheck hc)
  (match hc
    [(CHyp hᵒ mᵒ tᵒ)
     (define-values (hd-src hd-tgt) (object-hc-head-typecheck hᵒ))
     (define-values (md-src md-tgt) (object-hc-middle-typecheck mᵒ))
     (define-values (tl-src tl-tgt) (object-hc-tail-typecheck tᵒ))
     (unless (equal? hd-tgt md-src) (hc-typecheck-err "object" 'head-middle hc hd-tgt md-src))
     (unless (equal? md-tgt tl-src) (hc-typecheck-err "object" 'middle-tail hc md-tgt tl-src))
     (values hd-src tl-tgt)]))

(define (object-hc-head-typecheck h)
  (match h
    [(CProj Gᵒ ℓ) (values (Dyn) Gᵒ)]
    [(CId O) (values O O)]
    [_ (error 'object-hc-head-typecheck "Invalid object hypercoercion head: ~a" h)]))

(define (object-hc-middle-typecheck m)
  (define (recurse Cᵒ) (object-hypercoercion-typecheck Cᵒ))
  (match m
    [(CFun Cᵒ₁ Cᵒ₂)
     (define-values (O₂ O₁) (recurse Cᵒ₁))
     (define-values (O₁^ O₂^) (recurse Cᵒ₂))
     (values (Fun O₁ O₁^) (Fun O₂ O₂^))]
    [(CId (Dyn)) (values (Dyn) (Dyn))]
    [(CId (and base (Base ι)))
     (unless (dict-has-key? base-types ι) (invalid-obj-hc-middle-base-err m ι))
     (values base base)]
    [(CBot O₁ O₂ ℓ) (values O₁ O₂)]
    [_ (error 'object-hc-middle-typecheck "Invalid object hypercoercion middle: ~a" m)]))

(define (object-hc-tail-typecheck t)
  (match t
    [(CInj Gᵒ) (values Gᵒ (Dyn))]
    [(CId O) (values O O)]
    [_ (error 'object-hc-tail-typecheck "Invalid object hypercoercion tail: ~a" t)]))

(define (ec-hypercoercion-typecheck hcoerc ctx ec-subtypes)
  (match hcoerc
    [(CHyp hᵉ mᵉ tᵉ)
     (define-values (head-src head-tgt) (ec-hc-head-typecheck hᵉ ctx))
     (define-values (middle-src middle-tgt) (ec-hc-middle-typecheck mᵉ ctx ec-subtypes))
     (define-values (tail-src tail-tgt) (ec-hc-tail-typecheck tᵉ ctx))
     (unless (equal? head-tgt middle-src) (ec-hc-typecheck-err 'head-middle hcoerc head-tgt middle-src))
     (unless (equal? middle-tgt tail-src) (ec-hc-typecheck-err 'middle-tail hcoerc middle-tgt tail-src))
     (values head-src tail-tgt)]))

(define (ec-hc-head-typecheck h ctx)
  (match h
    [(CProj ec ℓ)
     #:when (well-formed-static-ec? ec ctx)
     (values (Dyn) ec)]
    [(CId ê)
     #:when (well-formed-ec? ê ctx)
     (values ê ê)]
    [_ (error 'ec-hc-head-typecheck "Invalid EC hypercoercion head: ~a" h)]))

(define (ec-hc-middle-typecheck m ctx ec-subtypes)
  (match m
    [(CSub ê ê^)
     (unless (ec-<: ê ê^ ec-subtypes) (ec-hc-middle-mismatch-err m ê ê^ ec-subtypes))
     (values ê ê^)]
    [(CBot ê ê^ ℓ)
     (unless (well-formed-ec? ê ctx) (ec-hc-bot-err 'invalid-src m ê))
     (unless (well-formed-ec? ê^ ctx) (ec-hc-bot-err 'invalid-tgt m ê^))
     (values ê ê^)]
    [_ (error 'ec-hc-middle-typecheck "Invalid EC hypercoercion middle: ~a" m)]))

(define (ec-hc-tail-typecheck t ctx)
  (match t
    [(CInj ec)
     #:when (well-formed-static-ec? ec ctx)
     (values ec (Dyn))]
    [(CId ê)
     #:when (well-formed-ec? ê ctx)
     (values ê ê)]
    [_ (error 'ec-hc-tail-typecheck "Invalid ec hypercoercion tail: ~a" t)]))

(define (ensure-well-typed-heap heap [ctx (hash)]
                                [Θ (unweighted-graph/directed '())]
                                [Σ (vector)])
  (define heap-size (vector-length heap))
  (define heap-types-size (vector-length Σ))
  (unless (eqv? heap-size heap-types-size) (ensure-wt-heap-err 'size-mismatch heap-size heap-types-size))
  (for ([a (in-range heap-size)])
    (define a-term (vector-ref heap a))
    (define a-type (meta-cc-typecheck a-term ctx Θ Σ))
    (define heap-type (vector-ref Σ a))
    (unless (meta-type-α-equiv? a-type heap-type)
      (ensure-wt-heap-err 'type-err a a-term heap-type a-type))))

(define (object-cc-typecheck-err key . args)
  (match* (key args)
    [('ovar-not-subtype (list α x ec ec-subtypes))
     (error 'object-cc-typecheck
            (string-append
             "The environment classifier ~a associated with object variable ~a"
             " was expected to be a subtype of ~a, but it "
             "actually is not.~nSubtypes: ~a~n")
            α x ec (get-edges ec-subtypes))]
    [('ec-exists (list term))
     (error 'object-cc-typecheck
              (string-append
               "In term:~n~v~nEnvironment classifier parameter is already used in "
               "scope. Use a fresh classifier name.")
              (unparse-object-term term))]
    [('ofixabs-return-type-mismatch (list T T^))
     (error 'object-cc-typecheck
              (string-append
               "In object fixpoint lambda:~n~v~nThe given return type ~a and actual "
               "type returned ~a are not the same")
              (unparse-object-type T)
              (unparse-object-type T^))]
    [('wrong-arg-type (list term S arg-type))
     (error 'object-cc-typecheck
            (string-append
             "In term:~n~v~nThe type of the argument should be the domain type of the function ~a, "
             "but found: ~a")
            (unparse-object-term term)
            (unparse-object-type S)
            (unparse-object-type arg-type))]
    [('wrong-fun-type (list term fun-type))
     (error 'object-cc-typecheck
               (string-append
                "In term:~n~v~nType of the function in application"
                "should be a function, but found:\n\t~a")
               (unparse-object-term term)
               (unparse-object-type fun-type))]
    [('if-test-not-bool (list term test-type))
     (error 'object-cc-typecheck
              (string-append
               "In term:~n~v~nThe type of the test expression should be Bool, "
               "but found: ~a")
              (unparse-object-term term)
              (unparse-object-type test-type))]
    [('wrong-if-branches (list term then-type else-type))
     (error 'object-cc-typecheck
            (string-append
             "In term:~n~v~nType of the then term ~a and else term ~a should "
             "be the same")
            (unparse-object-term term)
            (unparse-object-type then-type)
            (unparse-object-type else-type))]
    [('wrong-if-ann (list term then-type ann-type))
     (error 'object-cc-typecheck
            (string-append
             "In term:~n~v~nType of the then term ~a and type annotation ~a should "
             "be the same")
            (unparse-object-term term)
            (unparse-object-type then-type)
            (unparse-object-type ann-type))]
    [('wrong-splice-type (list term S))
     (error 'object-cc-typecheck
            (string-append
             "In term:~n~v~nThe type of the spliced term should be a "
             "code type, but found ~a")
            (unparse-object-term term)
            (unparse-meta-type S))]
    [('wrong-splice-ec (list term ec ec^))
     (error 'object-cc-typecheck
            (string-append
             "In term:~n~v~nThe code type of the spliced term should "
             "be associated with the surrounding EC ~a, but found ~a")
            (unparse-object-term term)
            ec ec^)]))
 
(define (meta-cc-typecheck-err key . args)
  (match* (key args)
    [('ill-formed-param-type (list term A))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nThe function parameter type annotation ~a "
             "is ill-formed")
            (unparse-meta-term term)
            (unparse-meta-type A))]
    [('ill-formed-return-type (list term B))
     (error
      'meta-cc-typecheck
      (string-append
       "In term:~n~v~nThe return type annotation ~a "
       "is ill-formed")
      (unparse-meta-term term)
      (unparse-meta-type B))]
    [('mismatched-return-type (list term B^ B))
     (error 'meta-cc-typecheck
              (string-append
               "In term:~n~v~nThe type of the body ~a should be "
               "α-equivalent to the declared return type ~a")
              (unparse-meta-term term)
              (unparse-meta-type B^)
              (unparse-meta-type B))]
    [('wrong-arg-type (list term P-type A₁))
     (error 'meta-cc-typecheck
                 (string-append
                  "In term:~n~v~nThe type of the application argument ~a should be "
                  "α-equivalent to the domain of the type of the function ~a")
                 (unparse-meta-term term)
                 (unparse-meta-type P-type)
                 (unparse-meta-type A₁))]
    [('wrong-fun-type (list term Q-type))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nExpected the type of the function in application to "
             "be a function, but got ~a")
            (unparse-meta-term term)
            (unparse-meta-type Q-type))]
    [('ec-param-exists (list term))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nEnvironment classifier parameter is already used "
             "in scope. Use a fresh classifier name.")
            (unparse-meta-term term))]
    [('ill-formed-static-ec (list term ec))
     (error 'meta-cc-typecheck "In term:~n~v~nEnvironment classifier ~a is an ill-formed static EC"
            (unparse-meta-term term) (unparse-ec ec))]
    [('ecapp-ub-fail (list term ec P-type))
     (error 'meta-cc-typecheck
            (string-append
             "in term:~n~v~nThe env classifier argument ~a should be "
             "a subtype of the upper bound in the universal type ~a")
            (unparse-meta-term term)
            (unparse-ec ec)
            (unparse-meta-type P-type))]
    [('ecapp-lb-fail (list term ec P-type))
     (error 'meta-cc-typecheck
            (string-append
             "in term:~n~v~nThe env classifier argument ~a should be "
             "a supertype of the lower bound in the universal type ~a")
            (unparse-meta-term term)
            (unparse-ec ec)
            (unparse-meta-type P-type))]
    [('wrong-ecapp-type (list term P-type))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nExpected the type of the EC abstraction in "
             "EC application to be ∀̇ or ?, but got ~a")
            (unparse-meta-term term)
            (unparse-meta-type P-type))]
    [('sub-elim-sub-fail (list term sub-ec sup-ec))
     (error 'meta-cc-typecheck
            "In sub-elim:~n~v~nSubtyping failed: ~a <: ~a"
            (unparse-meta-type term) (unparse-ec sub-ec) (unparse-ec sup-ec))]
    [('sub-elim-bad-type (list term P-type))
     (error 'meta-cc-typecheck "In sub-elim:~n~v~nExpected subtype constraint type, not ~a"
            (unparse-meta-term term) (unparse-meta-type P-type))]
    [('ref-mismatched-ann (list term A A^))
     (error 'meta-cc-typecheck "In term:~n~v~nAnnotated type ~a and actual type ~a are not α-equivalent"
            (unparse-meta-term term) (unparse-meta-type A) (unparse-meta-type A^))]
    [('set-types-mismatch (list term P-type A))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nThe type of the assignment RHS ~a should be "
             "α-equivalent to the type stored in the LHS reference ~a")
            (unparse-meta-term term)
            (unparse-meta-type P-type)
            (unparse-meta-type A))]
    [('wrong-set-lhs (list term Q-type))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nExpected the type of the LHS in "
             "assignment to be ̇Ref or ?, but got ~a")
            (unparse-meta-term term)
            (unparse-meta-type Q-type))]
    [('wrong-deref-type (list term P-type))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nExpected the type of the dereference"
             "argument to be ̇Ref or ?, but got ~a")
            (unparse-meta-term term)
            (unparse-meta-type P-type))]
    [('if-test-not-bool (list term A))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~nThe type of the condition ~a "
             "should be the type Bool")
            (unparse-meta-term term)
            (unparse-meta-type A))]
    [('wrong-if-branches (list term B₁ B₂))
     (error 'meta-cc-typecheck
              (string-append
               "In term:~n~v~nThe type of the then-branch ~a "
               "should be α-equivalent to the type of the else-branch ~a")
              (unparse-meta-term term)
              (unparse-meta-type B₁)
              (unparse-meta-type B₂))]
    [('wrong-if-ann (list term B₁ B))
     (error 'meta-cc-typecheck
              (string-append
               "In term:~n~v~nThe type of the then-branch ~a "
               "should be α-equivalent to the annotation type ~a")
              (unparse-meta-term term)
              (unparse-meta-type B₁)
              (unparse-meta-type B))]
    [('cast-coerc-mismatch (list term A src))
     (error 'meta-cc-typecheck
            (string-append
             "In term:~n~v~n The type of the casted term ~a should be "
             "α-equivalent to the source type ~a of the coercion")
            (unparse-meta-term term)
            (unparse-meta-type A)
            (unparse-meta-type src))]
    [('ill-formed-blame-ann (list term A))
     (error 'meta-cc-typecheck
            "In term:~n~v~nThe type annotation ~a is ill-formed"
            (unparse-meta-term term) (unparse-meta-type A))]
    [('loc-out-of-bounds (list addr heap-size))
     (error 'meta-cc-typecheck "Out of bounds address ~a for heap of size ~a" addr heap-size)]))

(define (hc-typecheck-err kind key hcoerc type1 type2)
  (define unparse-hc
    (cond
      [(equal? kind "meta") unparse-meta-hypercoercion]
      [(equal? kind "object" unparse-object-hypercoercion)]))
  (define unparse-type
    (cond
      [(equal? kind "meta") unparse-meta-type]
      [(equal? kind "object" unparse-object-type)]))
  (match key
    ['head-middle
     (error (string->symbol (string-append kind "-hypercoercion-typecheck"))
              (string-append
               "In hypercoercion:~n~v~nThe target type of the head coercion ~a should be "
               "α-equivalent to the source type of the middle coercion ~a")
              (unparse-hc hcoerc)
              (unparse-type type1)
              (unparse-type type2))]
    ['middle-tail
     (error (string->symbol (string-append kind "-hypercoercion-typecheck"))
              (string-append
               "In hypercoercion:~n~v~nThe target type of the middle coercion ~a should be "
               "α-equivalent to the source type of the tail coercion ~a")
              (unparse-hc hcoerc)
              (unparse-type type1)
              (unparse-type type2))]))

(define (meta-hc-hd-typecheck-err key . args)
  (match* (key args)
    [('bad-proj (list h G))
     (error
      'meta-hc-head-typecheck
      (string-append
       "In head coercion:~n~v~nThe type annotation ~a "
       "is not a well-formed gradual type")
      (unparse-meta-hc-head h)
      (unparse-meta-type G))]
    [('bad-id (list h A))
     (error
      'meta-hc-head-typecheck
      (string-append
       "In head coercion:~n~v~nThe type annotation ~a "
       "is not a well-formed type")
      (unparse-meta-hc-head h)
      (unparse-meta-type A))]))

(define (meta-hc-md-typecheck-err key . args)
  (match* (key args)
    [('write-tgt-mismatch (list m A A^))
     (error 'meta-hc-middle-typecheck
            (string-append
             "In middle coercion:~n~v~nThe target type of the write coer ~a "
             "and the source type of the read coercion ~a should be α-equivalent")
            (unparse-meta-hc-middle m)
            (unparse-meta-type A)
            (unparse-meta-type A^))]
    [('write-src-mismatch (list m B B^))
     (error 'meta-hc-middle-typecheck
            (string-append
             "In middle coercion:~n~v~nThe source type of the write coer ~a "
             "and the target type of the read coercion ~a should be α-equivalent")
            (unparse-meta-hc-middle m)
            (unparse-meta-type B)
            (unparse-meta-type B^))]
    [('invalid-ec-param (list m))
     (error 'meta-hc-middle-typecheck
            "In middle coercion:~n~v~nEnvironment classifier parameter cannot be ⋆ or ε"
            (unparse-meta-hc-middle m))]
    [('invalid-sub-ec (list m sub-ec))
     (error 'meta-hc-middle-typecheck
            "In coercion:~n~v~nSub environment classifier ~a is an ill-formed static EC"
            (unparse-meta-hc-middle m) sub-ec)]
    [('invalid-sup-ec (list m sup-ec))
     (error 'meta-hc-middle-typecheck
            "In coercion:~n~v~nSuper environment classifier ~a is an ill-formed static EC"
            (unparse-meta-hc-middle m) sup-ec)]
    [('<:-fail (list m sub-ec sup-ec))
     (error 'meta-hc-middle-typecheck
            "In coercion:~n~v~nThe subtype relation ~a <: ~a doesn't hold"
            (unparse-meta-hc-middle m) (unparse-ec sub-ec) (unparse-ec sup-ec))]
    [('ec-param-exists (list m))
     (error 'meta-hc-middle-typecheck
            (string-append
             "In coercion:~n~v~nEnvironment classifier parameter is already used "
             "in scope. Use a fresh classifier name.")
            (unparse-meta-hc-middle m))]
    [('bad-id-base (list m ι))
     (error
      'meta-hc-middle-typecheck
      (string-append
       "In middle coercion:~n~v~nThe type annotation ~a "
       "is not a valid base type")
      (unparse-meta-hc-middle m) ι)]
    [('bad-bot-src (list t A))
     (error
      'meta-hc-middle-typecheck
      (string-append
       "In middle coercion:~n~v~nThe source type annotation ~a "
       "is ill-formed")
      (unparse-meta-hc-middle t)
      (unparse-meta-type A))]
    [('bad-bot-tgt (list t B))
     (error
      'meta-hc-middle-typecheck
      (string-append
       "In middle coercion:~n~v~nThe target type annotation ~a "
       "is ill-formed")
      (unparse-meta-hc-middle t)
      (unparse-meta-type B))]))

(define (meta-hc-tl-typecheck-err key . args)
  (match* (key args)
    [('bad-inj (list t G))
     (error
      'meta-hc-tail-typecheck
      (string-append
       "In tail coercion:~n~v~nThe type annotation ~a "
       "is not a well-formed gradual type")
      (unparse-meta-hc-tail t)
      (unparse-meta-type G))]
    [('bad-id (list t A))
     (error
      'meta-hc-tail-typecheck
      (string-append
       "In tail coercion:~n~v~nThe type annotation ~a "
       "is not a well-formed type")
      (unparse-meta-hc-tail t)
      (unparse-meta-type A))]))

(define (invalid-obj-hc-middle-base-err m ι)
  (error
   'object-hc-middle-typecheck
   (string-append
    "In middle coercion:~n~v~nThe type annotation ~a "
    "is not a valid base type")
   (unparse-obj-hc-middle m) ι))

(define (ec-hc-typecheck-err key hc ec1 ec2)
  (match key
    ['head-middle
     (error 'ec-hypercoercion-typecheck
            (string-append
             "In hypercoercion:~n~v~nThe target EC of the head coercion ~a should be "
             "equal to the source EC of the middle coercion ~a")
            (unparse-ec-hypercoercion hc) ec1 ec2)]
    ['middle-tail
     (error 'ec-hypercoercion-typecheck
            (string-append
             "In hypercoercion:~n~v~nThe target EC of the middle coercion ~a should be "
             "equal to the source EC of the tail coercion ~a")
            (unparse-ec-hypercoercion hc) ec1 ec2)]))

(define (ec-hc-middle-mismatch-err m ê ê^ ec-subtypes)
  (error
   'ec-hc-middle-typecheck
   "In EC middle coercion:~n~v~nThe EC ~a should be a subtype of the EC ~a~nsubtype context:~n~a"
   (unparse-ec-hc-middle m) (unparse-ec ê) (unparse-ec ê^) (get-edges ec-subtypes)))

(define (ec-hc-bot-err key t ê)
  (match key
    ['invalid-src
     (error
      'ec-coercion-typecheck
      (string-append
       "In EC middle coercion:~n~v~nThe source EC annotation ~a "
       "is ill-formed")
      (unparse-ec-hc-middle t) (unparse-ec ê))]
    ['invalid-tgt
     (error
      'ec-coercion-typecheck
      (string-append
       "In EC middle coercion:~n~v~nThe target EC annotation ~a "
       "is ill-formed")
      (unparse-ec-hc-middle t) (unparse-ec ê))]))

(define (ensure-wt-heap-err key . args)
  (match* (key args)
    [('size-mismatch (list heap-size heap-types-size))
     (error 'ensure-well-typed-heap
            "The size of the heap and heap typing should be the same.~nHeap size:~a~nHeap typing size:~a~n"
            heap-size heap-types-size)]
    [('type-err (list a a-term heap-type a-type))
     (error
       'ensure-well-typed-heap
       (string-append
        "In term stored at address ~a in heap:~n~v~nExpected type from heap typing ~a "
        "should be same as the actual type of the stored term ~a")
       a (unparse-meta-term a-term) (unparse-meta-type heap-type) (unparse-meta-type a-type))]))

;; (require racket/trace)
;; (trace meta-cc-typecheck)
;; (trace object-cc-typecheck)
;; (trace ec->Γᵒ)
