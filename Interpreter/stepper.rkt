#lang racket
(require graph)
(require "utils.rkt")
(require "ast.rkt")
(require "parse.rkt")
(require (only-in "typecheck.rkt"
                  ec-≲ meta-elaborate surface->cc-type add-subtype primitives))
(require (except-in "typecheck-cast-calculus.rkt"
                    well-formed-meta-type?))
(require (only-in "sister-language/typecheck.rkt"
                  OType EC ecs-in-ctx))
(require (only-in "sister-language/evaluate.rkt"
                  object-evaluate^ FixClos))
(require "sister-language/logging.rkt")
(provide run unchecked-casts? multi-step)

;; When #t, EC cast checking is off ("NoCheck"): every cast behaves as the
;; identity on the carried value. Succeeding casts already preserve the
;; underlying value, so operationally only the would-blame points change: a
;; failing cast returns the carried value instead of reducing to blame, and
;; dynamic EC-subtype elimination proceeds as if the check had passed (or gets
;; stuck if the value cannot support the elimination). The per-step
;; type-preservation checks are skipped, since reduction need not preserve
;; types once failing casts act as identities. Evaluation may then produce
;; ill-scoped code, a wrong final result, or get stuck.
(define unchecked-casts? (make-parameter #f))

(define (source-of-head h)
  (match h
    [(CProj H ℓ) (Dyn)]
    [(CId A) A]))

(define (target-of-head h)
  (match h
    [(CProj H ℓ) H]
    [(CId A) A]))

(define (source-of-tail t)
  (match t
    [(CInj G) G]
    [(CId A) A]))

(define (target-of-tail t)
  (match t
    [(CInj G) (Dyn)]
    [(CId A) A]))

(define (compose-meta-coercion θ c d)
  (compose-*-coercion compose-meta-middle θ c d))

(define (compose-object-coercion θ c d)
  (compose-*-coercion compose-object-middle θ c d))

(define (compose-*-coercion comp-mid θ c d)
  (match* (c d)
    [((CHyp h1 (CBot A B ℓ) t1) (CHyp h2 m2 t2))
     (CHyp h1 (CBot A (source-of-tail t2) ℓ) t2)]
    [((CHyp h1 m1 t1) (CHyp h2 m2 t2))
     (match (compose-tail-head t1 h2)
       [(CId B)      (CHyp h1 (comp-mid θ m1 m2 (target-of-head h1) (source-of-tail t2)) t2)]
       [(CInj G)     (CHyp h1 m1 (CInj G))]
       [(CProj H ℓ)  (CHyp (CProj H ℓ) m2 t2)]
       [(CBot A B ℓ) (CHyp h1 (CBot (target-of-head h1) (source-of-tail t2) ℓ) t2)])]))

(define (compose-tail-head t h)
  (match* (t h)
    [(t (CId B)) t]
    [((CId A) h) h]
    [((CInj G) (CProj H ℓ))
     (cond [(meta-type-α-equiv? G H) (CId G)]
           [else (CBot G H ℓ)])]))

(define (compose-meta-middle θ m1 m2 src-type tgt-type)
  (define (⊥ ℓ) (CBot src-type tgt-type ℓ))
  (match* (m1 m2)
    [(m1 (CId B))
     m1]
    [((CId A) m2)
     m2]
    [((CFun c1 c2) (CFun d1 d2))
     (CFun (compose-meta-coercion θ d1 c1) (compose-meta-coercion θ c2 d2))]
    [((CRefT c1 c2) (CRefT d1 d2))
     (CRefT (compose-meta-coercion θ d1 c1) (compose-meta-coercion θ c2 d2))]
    [((CCode c1 ec1) (CCode c2 ec2))
     (match* ((compose-object-coercion θ c1 c2) (compose-ec-coercion θ ec1 ec2))
       [((CHyp hᵒ (CBot A B ℓ) tᵒ) _) (⊥ ℓ)]
       [(_ (CHyp hᵉ (CBot ec1 ec2 ℓ) tᵉ)) (⊥ ℓ)]
       [(c ec) (CCode c ec)])]
    [((CECUniv α c1) (CECUniv β c2))
     (CECUniv α (compose-meta-coercion θ c1 (coerce-rename-ec c2 β (ECVar α))))]
    [((CECSub sub-ec1 sup-ec1 c1) (CECSub sub-ec2 sup-ec2 c2))
     (CECSub sub-ec1 sup-ec1 (compose-meta-coercion (add-subtype θ sub-ec1 sup-ec1) c1 c2))]
    [((CBot A B ℓ) m)
     (⊥ ℓ)]
    [(m (CBot A B ℓ))
     (⊥ ℓ)]))

(define (compose-object-middle θ m1 m2 src-type tgt-type)
  (define (⊥ ℓ) (CBot src-type tgt-type ℓ))
  (match* (m1 m2)
    [(m1 (CId C))    m1]
    [((CId C) m2)    m2]
    [((CFun c1 c2) (CFun d1 d2))
     (match* ((compose-object-coercion θ d1 c1) (compose-object-coercion θ c2 d2))
       [((CHyp h m (CBot C1 C2 ℓ)) _) (⊥ ℓ)]
       [(_ (CHyp h m (CBot C1 C2 ℓ))) (⊥ ℓ)]
       [(c d) (CFun c d)])]
    [((CBot C1 C2 ℓ) mᵒ)
     (⊥ ℓ)]
    [(mᵒ (CBot C1 C2 ℓ))
     (⊥ ℓ)]))

(define (compose-ec-coercion θ ec1 ec2)
  (match* (ec1 ec2)
    [((CHyp h1 (CBot ec1 ec2 ℓ) t1) (CHyp h2 m2 t2))
     (CHyp h1 (CBot ec1 (source-of-tail t2) ℓ) t2)]
    [((CHyp h1 m1 t1) (CHyp h2 m2 t2))
     (define src-t2 (source-of-tail t2))
     (define tgt-h1 (target-of-head h1))
     (match (compose-ec-tail-head θ t1 h2)
       [(CSub ec1 ec2)
        (define m3 (compose-ec-middle (CSub ec1 ec2) m2 ec1 src-t2))
        (define m4 (compose-ec-middle m1 m3 tgt-h1 src-t2))
        (CHyp h1 m4 t2)]
       [(CId ec)  (CHyp h1 (compose-ec-middle m1 m2 tgt-h1 src-t2) t2)]
       [(CInj ec)  (CHyp h1 m1 (CInj ec))]
       [(CProj ec ℓ) (CHyp (CProj ec ℓ) m2 t2)]
       [(CBot ec1 ec2 ℓ) (CHyp h1 (CBot (target-of-head h1) (source-of-tail t2) ℓ) t2)])]))

(define (compose-ec-tail-head θ t h)
  (match* (t h)
    [(t (CId B)) t]
    [((CId A) h) h]
    [((CInj ec1) (CProj ec2 ℓ))
     (cond [(ec-≲ ec1 ec2 θ) (CSub ec1 ec2)]
           [else (CBot ec1 ec2 ℓ)])]))

(define (compose-ec-middle m1 m2 src-ec tgt-ec)
  (define (⊥ ℓ) (CBot src-ec tgt-ec ℓ))
  (match* (m1 m2)
    [((CSub e1 e2) (CSub e3 e4))
     (CSub e1 e4)]
    [((CBot e1 e2 ℓ) mᵉ)
     (⊥ ℓ)]
    [(mᵉ (CBot e1 e2 ℓ))
     (⊥ ℓ)]))

(define (stlc-term? ast)
  (match ast
    [(OVar id) #t]
    [(OAbs ec-param param param-t body)
     (stlc-term? body)]
    [(OFixAbsVal _ _ _ _ _ _ body)
     (stlc-term? body)]
    [(Const c) #t]
    [(AppAnn rator rand A) (and (stlc-term? rator) (stlc-term? rand))]
    [(IfAnn test then else A)
     (and (stlc-term? test) (stlc-term? then) (stlc-term? else))]
    [_ #f]))

(define (uncoerced-value? v)
  (match v
    [(Const _) #t]
    [(Prim _ _ _ _) #t]
    [(Quote Mᵒ ec) (stlc-term? Mᵒ)]
    [(MFixAbs f x A B M) #t]
    [(MAbs x A body) #t]
    [(ECAbsCC α N) #t]
    [(ECSubIntro sub-ec sup-ec N) #t]
    [(Loc a) #t]
    [_ #f]))

(define (inert? c)
  (match c
    [(CHyp (CId A) m (CInj G))
     #:when (not (CBot? m)) 
     #t]
    [(CHyp (CId A) m (CId B))
     #:when (and (not (CId? m)) (not (CBot? m))) 
     #t]
    [else #f]))

(define (value? v)
  (match v
    [(Cast U c)
     (and (uncoerced-value? U) (inert? c))]
    [else (uncoerced-value? v)]))

(define (apply-prim prim arg)
  (match prim
    [(Prim (cons arg-t '()) ret-t f _) (f arg)]
    [(Prim (cons arg-t args-t) ret-t f name)
     (Prim args-t ret-t (f arg) name)]))

(define (meta-reduce e Γ Θ Σ μ)
  (match e
    [(App (MFixAbs f x A B N) W) #:when (value? W)
     (values (term-subst (term-subst N f (MFixAbs f x A B N)) x W)
             Γ Θ Σ μ)]

    [(App p W) #:when (and (value? W) (Prim? p))
     (values (apply-prim p W) Γ Θ Σ μ)]

    [(IfAnn (Const b) M N A)
     (values (if b M N) Γ Θ Σ μ)]

    [(ECApp (ECAbsCC α P) ec2)
     (values (term-ec-rename P α ec2) Γ Θ Σ μ)]

    [(ECSubElim (ECSubIntro sub-ec sup-ec P))
     (values P Γ Θ Σ μ)]

    [(RefAnn V A) #:when (value? V)
     (values (Loc (vector-length μ))
             Γ Θ
             (vector-extend Σ (add1 (vector-length Σ)) A)
             (vector-extend μ (add1 (vector-length μ)) V))]

    [(Deref (Loc addr))
     (values (vector-ref μ addr) Γ Θ Σ μ)]

    [(Set (Loc addr) V) #:when (value? V)
     (values (Const '()) Γ Θ Σ (vector-set/copy μ addr V))]

    ;; Cast Reduction Rules

    ;; compose
    [(Cast (Cast M c) d)
     (values (Cast M (compose-meta-coercion Θ c d))
             Γ Θ Σ μ)]
    
    ;; identity
    [(Cast U (CHyp (CId A) (CId B) (CId C))) #:when (uncoerced-value? U)
     (values U Γ Θ Σ μ)]
    
    ;; blame; with cast checking off the failing cast acts as the identity
    [(Cast U (CHyp (CId A) (CBot B C ℓ) t)) #:when (uncoerced-value? U)
     (cond [(unchecked-casts?)
            (log debug "unchecked: failing cast acts as identity (label ~a)" (unparse-label ℓ))
            (values U Γ Θ Σ μ)]
           [else
            (values (Blame (target-of-tail t) ℓ) Γ Θ Σ μ)])]
    
    ;; wrap function
    [(App (and v (Cast u (CHyp (CId _) (CFun c d) (CId _)))) w) #:when (and (value? v) (value? w))
     (values (Cast (App u (Cast w c)) d)
             Γ Θ Σ μ)]

    ;; Deref Cast
    [(Deref (and v (Cast u (CHyp h (CRefT c d) t)))) #:when (value? v)
     (values (Cast (Deref u) d) Γ Θ Σ μ)]

    ;; Set Cast
    [(Set (and v (Cast u (CHyp h (CRefT c d) t))) W) #:when (and (value? v) (value? W))
     (values (Set u (Cast W c)) Γ Θ Σ μ)]

    ;; univ coercion and EC application
    [(ECApp (and V (Cast U (CHyp (CId A) (CECUniv α C) (CId B)))) ec) #:when (value? V)
     (values (Cast (ECApp U ec) (coerce-rename-ec C α ec))
             Γ Θ Σ μ)]

    [(ECSubElim (and V (Cast U (CHyp (CId A) (CECSub sub-ec^ sup-ec^ C) (CId B))))) #:when (value? V)
     (values (Cast (ECSubElim U) C)
             Γ Θ Σ μ)]

    [(ECSubElimDyn (and V (Cast U (CHyp h m (CInj (ECSub sub-ec sup-ec (Dyn)))))) ℓ)
     #:when (and (value? V) (ec-<: sub-ec sup-ec Θ))
     (values (ECSubElim (Cast U (CHyp h m (CId (ECSub sub-ec sup-ec (Dyn))))))
             Γ Θ Σ μ)]

    [(ECSubElimDyn (and V (Cast U (CHyp h m (CInj (ECSub sub-ec sup-ec (Dyn)))))) ℓ)
     #:when (and (value? V) (not (ec-<: sub-ec sup-ec Θ)))
     (log debug "Dynamic subtype check failed: ~a <: ~a" (unparse-ec sub-ec) (unparse-ec sup-ec))
     (cond [(unchecked-casts?)
            ;; proceed as if the subtype check had succeeded
            (values (ECSubElim (Cast U (CHyp h m (CId (ECSub sub-ec sup-ec (Dyn))))))
                    Γ Θ Σ μ)]
           [else
            (values (Blame (Dyn) ℓ) Γ Θ Σ μ)])]

    [(ECSubElimDyn (and V (Cast U (CHyp h m (CInj A)))) ℓ) #:when (value? V)
     (log debug "subtype elim, expected injected subtype constraint, not: ~a" (unparse-meta-type A))
     (cond [(unchecked-casts?)
            ;; attempt the elimination on the raw value; may get stuck
            (values (ECSubElim U) Γ Θ Σ μ)]
           [else
            (values (Blame (Dyn) ℓ) Γ Θ Σ μ)])]

    ;; quote-fail
    [(Quote (Splice (Blame A ℓ)) ec)
     (values (Blame A ℓ) Γ Θ Σ μ)]

    ;; Blame propagation rules
    
    [(App (Blame (Fun A B) ℓ) M)
     (values (Blame B ℓ) Γ Θ Σ μ)]

    [(App (MFixAbs f x A B M) (Blame C ℓ))
     (values (Blame B ℓ) Γ Θ Σ μ)]

    [(ECApp (Blame (ECUniv α lb ub A) ℓ) ec)
     (values (Blame (type-ec-rename A α ec) ℓ) Γ Θ Σ μ)]

    [(RefAnn (Blame A ℓ) B)
     (values (Blame (RefT A) ℓ) Γ Θ Σ μ)]

    [(Set (Blame A ℓ) M)
     (values (Blame (Base 'Unit) ℓ) Γ Θ Σ μ)]

    [(Set V (Blame A ℓ)) #:when (value? V)
     (values (Blame (Base 'Unit) ℓ) Γ Θ Σ μ)]

    [(Deref (Blame (RefT A) ℓ))
     (values (Blame A ℓ) Γ Θ Σ μ)]

    [(IfAnn (Blame A ℓ) M N B)
     (values (Blame B ℓ) Γ Θ Σ μ)]

    [(Cast (Blame A ℓ) (CHyp h m t))
     (values (Blame (target-of-tail t) ℓ) Γ Θ Σ μ)]

    ;; congruence rules
    
    [(Quote Mᵒ ec)
     (define-values (Mᵒ^ Γ^ Θ^ Σ^ μ^) (code-reduce Mᵒ ec Γ Θ Σ μ))
     (values (Quote Mᵒ^ ec) Γ^ Θ^ Σ^ μ^)]

    [(Cast M c)
     (define-values (M^ Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
     (values (Cast M^ c) Γ^ Θ^ Σ^ μ^)]
    
    [(RefAnn M A)
     (define-values (M^ Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
     (values (RefAnn M^ A) Γ^ Θ^ Σ^ μ^)]

    [(Deref M)
     (define-values (M^ Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
     (values (Deref M^) Γ^ Θ^ Σ^ μ^)]

    [(Set L M)
     (cond [(value? L)
            (define-values (M^ Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
            (values (Set L M^) Γ^ Θ^ Σ^ μ^)]
           [else
            (define-values (L^ Γ^ Θ^ Σ^ μ^) (meta-reduce L Γ Θ Σ μ))
            (values (Set L^ M) Γ^ Θ^ Σ^ μ^)])]
    
    [(App L M)
     (cond [(value? L)
            (define-values (M^ Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
            (values (App L M^) Γ^ Θ^ Σ^ μ^)]
           [else
            (define-values (L^ Γ^ Θ^ Σ^ μ^) (meta-reduce L Γ Θ Σ μ))
            (values (App L^ M) Γ^ Θ^ Σ^ μ^)])]

    [(IfAnn L M N A)
     (define-values (L^ Γ^ Θ^ Σ^ μ^) (meta-reduce L Γ Θ Σ μ))
     (values (IfAnn L^ M N A) Γ^ Θ^ Σ^ μ^)]

    [(ECApp M ec)
     (define-values (M^ Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
     (values (ECApp M^ ec) Γ^ Θ^ Σ^ μ^)]

    [(ECSubElim P)
     (define-values (P^ Γ^ Θ^ Σ^ μ^) (meta-reduce P Γ Θ Σ μ))
     (values (ECSubElim P^) Γ^ Θ^ Σ^ μ^)]

    [(ECSubElimDyn P ℓ)
     (define-values (P^ Γ^ Θ^ Σ^ μ^) (meta-reduce P Γ Θ Σ μ))
     (values (ECSubElimDyn P^ ℓ) Γ^ Θ^ Σ^ μ^)]
     
    [else
     (error 'meta-reduce "not reducible ~a" e)]
    ))

(define (code-reduce M e Γ Θ Σ μ)
  (match M
    ;; splice-β
    [(Splice (Quote Vᵒ e′)) #:when (stlc-term? Vᵒ)
     (values Vᵒ Γ Θ Σ μ)]

    ;; splice-code-sub
    [(Splice (Cast (Quote M e^) c)) #:when (and (stlc-term? M) (inert? c))
     (values M Γ Θ Σ μ)]

    ;; code-λ
    [(OFixAbs α f β x A B N)
     (define α^ (gen-id α))
     (define β^ (gen-id β))
     (define f^ (gen-id f))
     (define x^ (gen-id x))
     (define Θ^ (add-subtype (add-subtype Θ e (ECVar α^)) (ECVar α^) (ECVar β^)))
     (define Γ^ (dict-set* Γ
                           α^ (EC)
                           f^ (OType (Fun A B) β^)
                           β^ (EC)
                           x^ (OType A α^)))
     (define N^ (term-subst
                 (term-ec-rename
                  (term-subst
                   (term-ec-rename
                    N
                    α (ECVar α^))
                   f (OVar f^))
                  β (ECVar β^))
                 x (OVar x^)))
     (values (OFixAbsVal α^ f^ β^ x^ A B N^) Γ^ Θ^ Σ μ)]

    ;; Blame propagation rules

    [(AppAnn (Splice (Blame _ ℓ)) M C)
     (values (Splice (Blame (Code C e) ℓ)) Γ Θ Σ μ)]

    [(AppAnn Vᵒ (Splice (Blame _ ℓ)) C) #:when (stlc-term? Vᵒ)
     (values (Splice (Blame (Code C e) ℓ)) Γ Θ Σ μ)]

    [(IfAnn (Splice (Blame _ ℓ)) M N C)
     (values (Splice (Blame (Code C e) ℓ)) Γ Θ Σ μ)]

    [(IfAnn Vᵒ (Splice (Blame _ ℓ)) N C) #:when (stlc-term? Vᵒ)
     (values (Splice (Blame (Code C e) ℓ)) Γ Θ Σ μ)]

    [(IfAnn Vᵒ Wᵒ (Splice (Blame _ ℓ)) C) #:when (and (stlc-term? Vᵒ) (stlc-term? Wᵒ))
     (values (Splice (Blame (Code C e) ℓ)) Γ Θ Σ μ)]

    [(OFixAbsVal α f β x A B (Splice (Blame _ ℓ)))
     (values (Splice (Blame (Code (Fun A B) e) ℓ)) Γ Θ Σ μ)]

    ;; congruence rules

    [(AppAnn L M A)
     (cond [(stlc-term? L)
            (define-values (M^ Γ^ Θ^ Σ^ μ^) (code-reduce M e Γ Θ Σ μ))
            (values (AppAnn L M^ A) Γ^ Θ^ Σ^ μ^)]
           [else
            (define-values (L^ Γ^ Θ^ Σ^ μ^) (code-reduce L e Γ Θ Σ μ))
            (values (AppAnn L^ M A) Γ^ Θ^ Σ^ μ^)])]
    [(IfAnn L M N A)
     (cond [(stlc-term? L)
            (cond [(stlc-term? M)
                   (define-values (N^ Γ^ Θ^ Σ^ μ^) (code-reduce N e Γ Θ Σ μ))
                   (values (IfAnn L M N^ A) Γ^ Θ^ Σ^ μ^)]
                  [else 
                   (define-values (M^ Γ^ Θ^ Σ^ μ^) (code-reduce M e Γ Θ Σ μ))
                   (values (IfAnn L M^ N A) Γ^ Θ^ Σ^ μ^)])]
           [else
            (define-values (L^ Γ^ Θ^ Σ^ μ^) (code-reduce L e Γ Θ Σ μ))
            (values (IfAnn L^ M N A) Γ^ Θ^ Σ^ μ^)])]
                    
    [(OFixAbsVal α f β x A B M)
     (define-values (M^ Γ^ Θ^ Σ^ μ^) (code-reduce M (ECVar β) Γ Θ Σ μ))
     (values (OFixAbsVal α f β x A B M^) Γ^ Θ^ Σ^ μ^)]

    [(Splice M)
     (define-values (M^ Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
     (values (Splice M^) Γ^ Θ^ Σ^ μ^)]

    [else
     (error 'code-reduce "not reducible ~a" M)]
    ))

(define multi-step
  (lambda (M M-type log-file Γ Θ Σ μ)
    (cond [(value? M)
           M]
          [else
           (define-values (res Γ^ Θ^ Σ^ μ^) (meta-reduce M Γ Θ Σ μ))
           (match res
             [(Blame A ℓ)
              (write-string (string-append "\\longmapsto &\\;"
                                           "\\mathbf{blame}^{" (unparse-label ℓ) "}")
                            log-file)
              (Blame A ℓ)]
             [_
              (write-string "\\longmapsto &\\;" log-file)
              (write-string (print-term res) log-file)
              (write-string "\\\\ \n" log-file)

              (cond
                [(unchecked-casts?)
                 ;; erased casts break type preservation by design, so the
                 ;; per-step metatheory checks do not apply in unchecked mode
                 (multi-step res #f log-file Γ^ Θ^ Σ^ μ^)]
                [else
                 (define res-type (meta-cc-typecheck res Γ^ Θ^ Σ^))
                 (ensure-reduction-preserves-type M-type res-type M res)
                 (ensure-well-typed-heap μ^ Γ^ Θ^ Σ^)

                 (multi-step res res-type log-file Γ^ Θ^ Σ^ μ^)])])]
          )))

(define (ensure-reduction-preserves-type e-type res-type e res)
  (unless (meta-type-α-equiv? e-type res-type)
    (error 'multi-step
           (string-append
            "The term:~n~v~nEsteps to the term:~n~v~n"
            "However, the first term's type ~a doesn't match with the second "
            "term's type ~a")
           (unparse-meta-term e) (unparse-meta-term res)
           (unparse-meta-type e-type) (unparse-meta-type res-type))))

(define (object-evaluate term [env (hasheqv)])
  (define (recurse term^) (object-evaluate term^ env))
  (match term
    [(OFixAbsVal α f β x A B M) (FixClos f x M env)]
    [(AppAnn M N _)
     (define evald-M (recurse M))
     (define evald-N (recurse N))
     (apply-fun evald-M evald-N)]
    [(IfAnn L M N _)
     (define b (Const-name (recurse L)))
     (cond
       [b (recurse M)]
       [else (recurse N)])]
    [(OVar x) (dict-ref env x)]
    [(Const k)
     (cond
       [(dict-has-key? primitives k)
        (dict-ref primitives k)]
       [else (Const k)])]
    ))


(define (apply-fun fun arg)
  (match fun
    [(FixClos f x M env^)
     (object-evaluate M (dict-set (dict-set env^ x arg)
                                  f (FixClos f x M env^)))]
    [(Prim _ _ _ _)
     (apply-prim fun arg)]))

(define (run surface-prog file-name)
  (call-with-output-file file-name #:exists 'replace
    (lambda (out-file)
      ;(display "source program:")(newline)
      ;(display (unparse-meta-term surface-prog))(newline)
      ;(display surface-prog)(newline)
      (dynamic-wind
       (λ ()
         (write-string "\\documentclass{article}\n" out-file)
         (write-string "\\usepackage{amsmath}\n" out-file)
         (write-string "\\usepackage{fullpage}\n" out-file)
         (write-string "\\allowdisplaybreaks\n" out-file)
         (write-string "\\DeclareMathSymbol{\\mlq}{\\mathord}{operators}{``}" out-file)
         (write-string "\\DeclareMathSymbol{\\mrq}{\\mathord}{operators}{`'}" out-file)
         (write-string "\\newcommand{\\quot}[1]{\\mlq\\mlq #1 \\mrq\\mrq}" out-file)
         (write-string "\\begin{document}\n" out-file)
         (write-string "\\tiny\\begin{align*}\n" out-file)
         (write-string (string-append "&" (print-term surface-prog) "\\\\ \n") out-file)
         (write-string (string-append "&" "\\Downarrow" "\\\\ \n") out-file))
      (λ ()
        (define Θ (unweighted-graph/directed '()))
        (define μ (vector))
        (define Σ (vector))
        (define Γ (hash))
        (define-values (cc-prog type) (meta-elaborate surface-prog Γ Θ))
        (write-string (string-append "&" (print-term cc-prog) "\\\\ \n") out-file)
        (define cc-type (meta-cc-typecheck cc-prog Γ Θ Σ))
        (define type^ (surface->cc-type type))
        (ensure-elab-preserves-types type^ cc-type surface-prog cc-prog)
        (match (multi-step cc-prog cc-type out-file Γ Θ Σ μ)
           [(Quote (? stlc-term? Mᵒ) _) (object-evaluate Mᵒ)]
           [(Cast (Quote (? stlc-term? Mᵒ) _) (? inert?)) (object-evaluate Mᵒ)]
           [res res]))
      (λ ()
        (write-string "\\end{align*}\n" out-file)
        (write-string "\\end{document}\n" out-file)))
      )))

(define (ensure-elab-preserves-types surface-type cc-type surface-prog cc-prog)
  (unless (meta-type-α-equiv? surface-type cc-type)
    (error 'run
           (string-append
            "The surface program:~n~v~nElaborates to the cast calculus program:~n~v~n"
            "However, the surface program's type ~a doesn't match with the cast calculus "
            "program's type ~a")
           (unparse-meta-term surface-prog) (unparse-meta-term cc-prog)
           (unparse-meta-type surface-type) (unparse-meta-type cc-type))))

;; (require racket/trace)
;; (trace meta-reduce)
;; (trace code-reduce)
;; (trace compose-meta-coercion)
;; (trace compose-meta-middle)
;; (trace compose-tail-head)
;; (trace object-evaluate)

