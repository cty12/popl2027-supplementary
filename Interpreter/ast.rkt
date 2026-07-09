#lang racket

(require racket/fixnum)
(require "utils.rkt")
(require "sister-language/logging.rkt")

(provide (all-defined-out))

;; TODO: Do a bunch of variations on higher-order-code-cast.lar to check various hypercoercion reductions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Surface Language Abstract Syntax                              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
variables                  x,y,f   : symbol
env classifier variables   α,β,γ   : symbol
blame labels               ℓ       : srcloc
environment classifiers    e       ::= (ECEps) | (ECVar α)
optional EC                e?      ::= e | #f
gradual env classifiers    ê       ::= e | (Dyn)
base types                 ι       ∈ (dict-keys base-types)
constants                  k       ∈ { k | ∃ pred ∈ (dict-values base-types). (pred k) ∨
                                           k ∈ (dict-keys prim-*-types) }
code lang types            S,T     ::= (Base ι) | (Fun S T)
gradual code types         C       ::= (Base ι) | (Fun C C) | (Dyn)
metalang types             A,B     ::= (Base ι) | (Fun A B) | (RefT A)
                                     | (Code C ê) | (ECUniv α e? e? A) | (Dyn)

code let* binders          Dᵒ       ::= (LetBind x Mᵒ) | (LetBindType x T Mᵒ) | (LetBindα x α Mᵒ)
                                      | (LetBindαType x α T Mᵒ)
meta let* binders          D        ::= (LetBind x M) | (LetBindTypeℓ x T M label)
code language terms        Mᵒ,Nᵒ,Lᵒ ::= (Const k) | (OVar x) | (OAbs α x T Mᵒ) | (OFixAbs α f β x S T Mᵒ)
                                      | (App Mᵒ Nᵒ) | (If Lᵒ Mᵒ Nᵒ) | (LetStar (Dᵒ...) Mᵒ)
                                      | (Spliceℓ M ℓ) | (Asc Mᵒ T)
metalanguage terms         M,N,L    ::= (Const k) | (MVar x) | (MAbs x A M) | (MFixAbsℓ f x A B M ℓ)
                                      | (Appℓ M N ℓ) | (ECAbs α e? e? M) | (ECAppℓ M e ℓ)
                                      | (Ref M) | (Setℓ M N ℓ) | (Derefℓ M ℓ)
                                      | (Ifℓ L M N ℓ) | (Quote Mᵒ e)
                                      | (LetStar (D...) M) | (Begin M... M)
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Cast Calculus Abstract Syntax                                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
primitive procedure        r       : {r | r is a procedure in Racket which performs a primitive operation}
variables                  x,y,f   : symbol
env classifier variables   α,β,γ   : symbol
blame labels               ℓ       : Label
addresses                  a       : ℕ
environment classifiers    e       ::= (ECEps) | (ECVar α)
gradual env classifiers    ê       ::= e | (Dyn)
base types                 ι       ∈ (dict-keys base-types)
constants                  k       ∈ { k | ∃ pred ∈ (dict-values base-types). (pred k) ∨
                                           k ∈ (dict-keys prim-*-types) }
primitives                 p       ∈ (dict-keys prim-*-types)
code lang types            S,T     ::= (Base ι) | (Fun S T)
gradual code types         C       ::= (Base ι) | (Fun C C) | (Dyn)
meta lang types            A,B     ::= (Base ι) | (Fun A B) | (RefT A)
                                     | (Code C ê) | (ECUnivCC α A) | (ECSub e e A) | (Dyn)
atomic types               atm     ::= (Base ι) | (Dyn) 

ground types               G,H      ::= (Base ι) | (Fun (Dyn) (Dyn)) | (RefT (Dyn))
                                      | (Code (Dyn) (Dyn)) | (ECUnivCC α (Dyn)) | (ECSub e e (Dyn)) | (Dyn)
code ground types          Gᵒ,Hᵒ    ::= (Base ι) | (Fun (Dyn) (Dyn))

code language terms        Mᵒ,Nᵒ,Lᵒ ::= (Const k) | (OVar x) | (OFixAbs α f β x S T Mᵒ)
                                      | (OFixAbsVal α f β x S T Mˢ)
                                      | (AppAnn Mᵒ Nᵒ T) | (IfAnn Lᵒ Mᵒ Nᵒ T) | (Splice M) | (Blame S ℓ)

STLC terms                 Mˢ       ::= (Const k) | (OVar x) | (OFixAbsVal α f β x S T Mˢ)
                                      | (AppAnn Mˢ Mˢ T) | (IfAnn Mˢ Mˢ Mˢ T)

metalanguage terms         M,N,L    ::= (Const k) | (Prim (ι ...) ι r p) | (MVar x) | (Loc a)
                                      | (MFixAbs f x A B M)
                                      | (App M N) | (ECAbsCC α M) | (ECApp M e)
                                      | (ECSubIntro e e M) | (ECSubElim M) | (ECSubElimDyn M ℓ)
                                      | (RefAnn M A) | (Set M N) | (Deref M)
                                      | (IfAnn L M N A) | (Quote Mᵒ e) 
                                      | (Cast M c) | (Blame A ℓ)

meta hypercoercions                  c ::= (CHyp h m t)
meta hypercoercion heads             h ::= (CProj G ℓ) | (Cid A)
meta hypercoercion middles           m ::= (CFun c c) | (CCode cᵒ cᵉ) | (CRefT c c)
                                         | (CECUniv α c) | (CECSub e e c) | (Cid atm)
meta hypercoercion tails             t ::= (CInj G) | (Cid A) | (CBot A B ℓ)

code hypercoercions                  cᵒ ::= (CHyp hᵒ mᵒ tᵒ)
code hypercoercion heads             hᵒ ::= (CProj Gᵒ ℓ) | (Cid C)
code hypercoercion middles           mᵒ ::= (CFun cᵒ cᵒ) | (Cid atm)
code hypercoercion tails             tᵒ ::= (CInj Gᵒ) | (Cid C) | (CBot C C ℓ)

ec hypercoercions                  cᵉ ::= (CHyp hᵉ mᵉ tᵉ)
ec hypercoercion heads             hᵉ ::= (CProj e ℓ) | (Cid ê)
ec hypercoercion middles           mᵉ ::= (CSub e e)
ec hypercoercion tails             tᵉ ::= (CInj e) | (Cid ê) | (CBot ê ê ℓ)
|#

(struct ECEps () #:transparent)
(struct ECVar (name) #:transparent)
(struct Dyn () #:transparent)
(struct Base (name) #:transparent)
(struct Fun (dom codom) #:transparent)
(struct RefT (type) #:transparent)
(struct Code (type ec) #:transparent)
(struct ECUniv (param lower upper type) #:transparent)
(struct LetBind (var rhs) #:transparent)
(struct LetBindType (var type rhs) #:transparent)
(struct LetBindTypeℓ (var type rhs label) #:transparent)
(struct LetBindα (var ec-param rhs) #:transparent)
(struct LetBindαType (var ec-param type rhs) #:transparent)
(struct Const (name) #:transparent)
(struct OVar (name) #:transparent)
(struct OAbs (ec-param param type body) #:transparent)
(struct OFixAbs (rec-ec-param rec-param ec-param param type ret-type body) #:transparent)
(struct App (fun arg) #:transparent)
(struct If (test then else) #:transparent)
(struct LetStar (bindings body) #:transparent)
(struct Splice (term) #:transparent)
(struct Spliceℓ (term label) #:transparent)
(struct Asc (term type) #:transparent)
(struct MVar (name) #:transparent)
(struct MAbs (param type body) #:transparent)
(struct MFixAbsℓ (rec-param param type ret-type body label) #:transparent)
(struct Appℓ (fun arg label) #:transparent)
(struct ECAbs (param lower upper body) #:transparent)
(struct ECAppℓ (term ec label) #:transparent)
(struct Ref (term) #:transparent)
(struct Setℓ (lhs rhs label) #:transparent)
(struct Derefℓ (term label) #:transparent)
(struct Ifℓ (test then else label) #:transparent)
(struct Quote (term ec) #:transparent)
(struct Begin (effects body) #:transparent)
(struct ECUnivCC (param type) #:transparent)
(struct ECSub (sub-ec sup-ec type) #:transparent)
(struct OFixAbsVal (rec-ec-param rec-param ec-param param type ret-type body) #:transparent)
(struct AppAnn (rator rand out-type) #:transparent)
(struct IfAnn (test then else out-type) #:transparent)
(struct MFixAbs (rec-param param type ret-type body) #:transparent)
(struct ECAbsCC (param body) #:transparent)
(struct ECApp (term ec) #:transparent)
(struct ECSubIntro (sub-ec sup-ec term) #:transparent)
(struct ECSubElim (term) #:transparent)
(struct ECSubElimDyn (term label) #:transparent)
(struct RefAnn (term type) #:transparent)
(struct Set (lhs rhs) #:transparent)
(struct Deref (term) #:transparent)
(struct Cast (term coerc) #:transparent)
(struct Blame (type label) #:transparent)
(struct CHyp (head middle tail) #:transparent)
(struct CProj (target label) #:transparent)
(struct CId (type) #:transparent)
(struct CFun (dom codom) #:transparent)
(struct CCode (obj-coerc ec-coerc) #:transparent)
(struct CRefT (write-coer read-coer) #:transparent)
(struct CECUniv (param-ec coer) #:transparent)
(struct CECSub (sub-ec sup-ec coer) #:transparent)
(struct CInj (source) #:transparent)
(struct CBot (source target label) #:transparent)
(struct CSub (ec-sub ec-sup) #:transparent)
(struct Loc (address) #:transparent)

(define (Label-source ℓ)
  (define path-or-str (srcloc-source (Label-srcloc ℓ)))
  (if (path? path-or-str) (path->string path-or-str) path-or-str))

(define (Label-line ℓ)
  (srcloc-line (Label-srcloc ℓ)))

(struct Label (srcloc) #:transparent
  #:methods
  gen:equal+hash
  [(define (equal-proc ℓ1 ℓ2 equal?-recur)
     (and (equal?-recur (Label-source ℓ1) (Label-source ℓ2))
          (equal?-recur (Label-line ℓ1) (Label-line ℓ2))))
   (define (hash-proc ℓ hash-recur)
     (fxxor (hash-recur (Label-source ℓ))
            (hash-recur (Label-line ℓ))))
   (define (hash2-proc ℓ hash2-recur)
     (fxxor (hash2-recur (Label-source ℓ))
            (hash2-recur (Label-line ℓ))))])

;; Primitive
(struct Prim (args-t ;; list of symbols corresponding to base types
              ret-t  ;; symbol corresponding to a base type
              fun    ;; Curried racket procedure accepting "(length args-t)" number of
                     ;; values and returning a value
              name
              ) #:transparent)


(define (ec-rename ec β new-ec)
  (match ec
    [(ECVar α)
     (cond [(equal? α β)
            new-ec]
           [else (ECVar α)])]
    [_ ec]))

(define (type-ec-rename type β new-ec)
  (define (recurse t) (type-ec-rename t β new-ec))
  (match type
    [(Dyn) (Dyn)]
    [(ECUnivCC α A)
     (cond
       [(equal? α β)
        (log debug "type-ec-rename should not print this if its type argument is well formed")
        type]
       [else
        (ECUnivCC α (recurse A))])]
    [(ECSub ec1 ec2 A)
     (define ec2^ (ec-rename ec2 β new-ec))
     (define ec1^ (ec-rename ec1 β new-ec))
     (ECSub ec1^ ec2^ (recurse A))]
    [(RefT A) (RefT (recurse A))]
    [(Code T ec)
     (Code T (ec-rename ec β new-ec))]
    [(ECUniv α lb ub A)
     (cond
       [(equal? α β)
        (log debug "type-ec-rename should not print this if its type argument is well formed")
        type]
       [else
        (define ub^ (ec-rename ub β new-ec))
        (define lb^ (ec-rename lb β new-ec))
        (ECUniv α lb^ ub^ (recurse A))])]
    [(Base name) type]
    [(Fun A B) (Fun (recurse A) (recurse B))]
    [_ (error 'type-ec-rename "Invalid meta type:~n~v" type)]))

(define (ec-α-equiv? ec1 ec2 scope1 scope2)
  (match* (ec1 ec2)
    [((Dyn) (Dyn)) #t]
    [((ECEps) (ECEps)) #t]
    [((ECVar α) (ECVar β)) #:when (equal? α β)
     ;; Free ECs that are equal will be handled here
     #t]
    [((ECVar α) (ECVar β))
     (define α-pos (index-of scope1 ec1))
     (define β-pos (index-of scope2 ec2))
     (match* (α-pos β-pos)
       [(#f _) #f]
       [(_ #f) #f]
       [(m n) #:when (equal? m n) #t]
       [(_ _)
        (ec-α-equiv?-log 'pos-mismatch α β α-pos β-pos)
        #f])]
    [(_ _)
     (ec-α-equiv?-log 'ec-mismatch ec1 ec2)
     #f]))

(define (meta-type-α-equiv? A B [scope1 '()] [scope2 '()])
  (define (recurse A^ B^)
    (meta-type-α-equiv? A^ B^ scope1 scope2))
  (match* (A B)
    [((Dyn) (Dyn)) #t]
    [((Base name1) (Base name2)) (equal? name1 name2)]
    [((Fun dom1 codom1) (Fun dom2 codom2))
     (and (recurse dom1 dom2)
          (recurse codom1 codom2))]
    [((RefT type1) (RefT type2))
     (recurse type1 type2)]
    [((Code type1 ec1) (Code type2 ec2))
     (cond
       [(not (ec-α-equiv? ec1 ec2 scope1 scope2))
        (meta-type-α-equiv?-log 'code A B ec1 ec2)
        #f]
       [else (equal? type1 type2)])]
    [((ECUniv α ec-lower1 ec-upper1 body1)
      (ECUniv β ec-lower2 ec-upper2 body2))
     (cond
       [(not (ec-α-equiv? ec-upper1 ec-upper2 scope1 scope2))
        (meta-type-α-equiv?-log 'ec-univ-upper A B ec-upper1 ec-upper2)
        #f]
       [(not (ec-α-equiv? ec-lower1 ec-lower2 scope1 scope2))
        (meta-type-α-equiv?-log 'ec-univ-lower A B ec-lower1 ec-lower2)
        #f]
       [else (meta-type-α-equiv? body1 body2
                                 (cons (ECVar α) scope1)
                                 (cons (ECVar β) scope2))])]
    [((ECUnivCC α body1) (ECUnivCC β body2))
     (meta-type-α-equiv? body1 body2 (cons (ECVar α) scope1) (cons (ECVar β) scope2))]
    [((ECSub sub-ec1 sup-ec1 body1) (ECSub sub-ec2 sup-ec2 body2))
     (cond
       [(not (ec-α-equiv? sup-ec1 sup-ec2 scope1 scope2))
        (meta-type-α-equiv?-log 'ec-univ-sup A B sup-ec1 sup-ec2)
        #f]
       [(not (ec-α-equiv? sub-ec1 sub-ec2 scope1 scope2))
        (meta-type-α-equiv?-log 'ec-univ-sub A B sub-ec1 sub-ec2)
        #f]
       [else (recurse body1 body2)])]
    [(_ _)
     (log debug "Not α-equivalent types:~n~v~n~v" A B)
     #f]))

(define (ec-α-equiv?-log key . args)
  (match* (key args)
    [('pos-mismatch (list α β α-pos β-pos))
     (log debug
          (string-append
           "The EC variables ~a and ~a are not α-equiv because they are at different positions "
           "in scope: ~a and ~a, respectively")
          (id->symbol α) (id->symbol β) α-pos β-pos)]
    [('ec-mismatch (list ec1 ec2))
     (log debug "Not α-equivalent ECs: ~a and ~a" ec1 ec2)]))

(define (meta-type-α-equiv?-log key A B ec1 ec2)
  (match key
    ['code
     (log debug
          (string-append
           "The code types ~a and ~a are not α-equivalent because "
           "their respective env classifiers ~a and ~a are not α-equivalent")
          A B ec1 ec2)]
    ['ec-univ-upper
     (log debug
          (string-append
           "The universal types ~a and ~a are not α-equivalent because "
           "their respective env classifier upper bounds ~a and ~a are not α-equivalent")
          A B ec1 ec2)]
    ['ec-univ-lower
     (log debug
          (string-append
           "The universal types ~a and ~a are not α-equivalent because "
           "their respective env classifier lower bounds ~a and ~a are not α-equivalent")
          A B ec1 ec2)]
    ['ec-univ-sup
     (log debug
          (string-append
           "The subtype types ~a and ~a are not α-equivalent because "
           "their respective env classifier super ECs ~a and ~a are not α-equivalent")
          A B ec1 ec2)]
    ['ec-univ-sub
     (log debug
          (string-append
           "The subtype types ~a and ~a are not α-equivalent because "
           "their respective env classifier sub ECs ~a and ~a are not α-equivalent")
          A B ec1 ec2)]
    [_ (error 'meta-type-α-equiv?-log "Invalid error key: ~a" key)]))

(define (print-ec ec)
  (match ec
    [(ECVar α) (id->string α)]
    [(ECEps) "\\varepsilon"]
    [(Dyn) "\\star"]
    [else
     (error 'print-ec "unrecognized EC: ~a" ec)]))

(define (print-type typ)
  (match typ
    [(Base ι) (string-append "\\mathtt{" (symbol->string ι) "}")]
    [(Dyn) "\\star"]
    [(Fun A B)
     (string-append "(" (print-type A) "{\\to}"
                    (print-type B) ")")]
    [(Code A ec)
     (string-append
      "\\quot{" (print-type A) "}^{" (print-ec ec) "}")]
    [(RefT A)
     (string-append "(\\mathtt{Ref}\\, " (print-type A) ")")]
    [(ECUniv α lb ub A)
     (string-append "(\\forall\\,"
                    (print-bounds α lb ub) ".\\,"
                    (print-type A) ")")]
    [(ECUnivCC α A)
     (string-append "(\\forall\\," (id->string α) ".\\,"
                    (print-type A) ")")]
    [(ECSub sub-ec sup-ec A)
     (string-append (print-ec sub-ec) " <: " (print-ec sup-ec) "\\Rightarrow\\," (print-type A))]
    [else
     (error 'print-type "unmatched ~a" typ)]
    ))

(define (print-obj-param x α)
  (string-append (id->string x) "^{" (id->string α) "}"))

(define (print-binding binding [depth (print-depth)])
  (match binding
    [(LetBind x rhs)
     (define x^ (id->string x))
     (define rhs^ (print-term rhs (sub1 depth)))
     "TODO"]
    [(LetBindType x A rhs)
     (define x^ (id->string x))
     (define A^ (print-type A))
     (define rhs^ (print-term rhs (sub1 depth)))
     "TODO"]
    [(LetBindTypeℓ x A rhs label)
     (define x^ (id->string x))
     (define A^ (print-type A))
     (define rhs^ (print-term rhs (sub1 depth)))
     "TODO"]
    [(LetBindα x α rhs)
     (define x^ (id->string x))
     (define α^ (id->symbol α))
     (define rhs^ (print-term rhs (sub1 depth)))
     "TODO"]
    [(LetBindαType x α A rhs)
     (define x^ (id->string x))
     (define α^ (id->symbol α))
     (define A^ (print-type A))
     (define rhs^ (print-term rhs (sub1 depth)))
     "TODO"]))

(define (print-bounds param lower upper)
  (define lower-str (if (not lower)
                        ""
                        (string-append "<: " (print-ec lower))))
  (define upper-str (if (not upper)
                        ""
                        (string-append "<: " (print-ec upper))))
  (string-append lower-str (id->string param) upper-str))

(define (print-label ℓ)
  (match-define (Label (srcloc source line _ _ _)) ℓ)
  (format "\\text{~a:~a}" source line))

(define print-depth (make-parameter 20))

;; TODO: skip printing lambda bodies
(define (print-term M [depth (print-depth)])
  (cond
    [(zero? depth) "\\dots"]
    [else
     (match M
       [(Const (? integer? i))
        (number->string i)]
       [(Const '()) "\\mathtt{unit}"]
       [(Const (? symbol? prim)) (symbol->string prim)]
       [(Const #t) "\\mathtt{true}"]
       [(Const #f) "\\mathtt{false}"]
       [(App L M)
        (string-append "\\left(" (print-term L (sub1 depth)) "\\cdot "
                       (print-term M (sub1 depth)) "\\right)")]
       [(Appℓ L M ℓ)
        (string-append "\\left(" (print-term L (sub1 depth)) "\\cdot "
                       (print-term M (sub1 depth)) "\\right)")]
       [(AppAnn L M A)
        (string-append "\\left(" (print-term L (sub1 depth)) "\\cdot "
                       (print-term M (sub1 depth)) "\\right)")]
       [(OVar x) (id->string x)]
       [(MVar x) (id->string x)]
       [(OAbs α x A M)
        (string-append
         "\\left(\\begin{array}{l} \\lambda "
         "(" (print-obj-param x α) ":" (print-type A) ")\\\\"
         (print-term M (sub1 depth)) "\\end{array}\\right)")]
       [(MAbs x A M)
        (string-append
         "\\left(\\begin{array}{l} \\lambda\\; "
         "(" (id->string x) ":" (print-type A) ")"
         "\\\\" (print-term M (sub1 depth)) "\\end{array}\\right)")]
       [(OFixAbs α f β x A B M)
        (string-append
         "\\left(\\begin{array}{l} \\mathtt{fix}\\; "
         (print-obj-param f α) "(" (print-obj-param x β) ":" (print-type A) ")"
         ": " (print-type B) "\\\\"
         (print-term M (sub1 depth)) "\\end{array}\\right)")]
       [(OFixAbsVal α f β x A B M)
        (string-append
         "\\left(\\begin{array}{l} \\overline{\\mathtt{fix}}\\; "
         (print-obj-param f α) "(" (print-obj-param x β) ":" (print-type A) ")"
         ": " (print-type B) "\\\\"
         (print-term M (sub1 depth)) "\\end{array}\\right)")]
       [(MFixAbs f x A B M)
        (string-append
         "\\left(\\begin{array}{l} \\mathtt{fix}\\; "
         (id->string f) "(" (id->string x) ":" (print-type A) ")"
         ": " (print-type B) "\\\\"
         (print-term M (sub1 depth)) "\\end{array}\\right)")]
       [(MFixAbsℓ f x A B M ℓ)
        (string-append
         "\\left(\\begin{array}{l} \\mathtt{fix}\\; "
         (id->string f) "(" (id->string x) ":" (print-type A) ")"
         ": " (print-type B) "\\\\"
         (print-term M (sub1 depth)) "\\end{array}\\right)")]
       [(LetStar bindings body)
        (define bindings^ (map (λ (b) (print-binding b (sub1 depth))) bindings))
        (define body^ (print-term body (sub1 depth)))
        "TODO"]
       [(Begin effects body)
        (define effects^ (map (λ (t) (print-term t (sub1 depth))) effects))
        (define body^ (print-term body (sub1 depth)))
        "TODO"]
       [(Splice N)
        (string-append "(\\sim " (print-term N (sub1 depth)) ")")]
       [(Spliceℓ N ℓ)
        (string-append "(\\sim " (print-term N (sub1 depth)) ")")]
       [(If test then else)
        (string-append
         "\\left(\\begin{array}{l}"
         "\\mathtt{if}\\," (print-term test (sub1 depth)) "\\\\"
         "\\mathtt{then}\\," (print-term then (sub1 depth)) "\\\\"
         "\\mathtt{else}\\," (print-term else (sub1 depth))
         "\\end{array}\\right)")]
       [(IfAnn test then else A)
        (string-append
         "\\left(\\begin{array}{l}"
         "\\mathtt{if}\\," (print-term test (sub1 depth)) "\\\\"
         "\\mathtt{then}\\," (print-term then (sub1 depth)) "\\\\"
         "\\mathtt{else}\\," (print-term else (sub1 depth))
         "\\end{array}\\right)")]
       [(Ifℓ test then else ℓ)
        (string-append
         "\\left(\\begin{array}{l}"
         "\\mathtt{if}\\," (print-term test (sub1 depth)) "\\\\"
         "\\mathtt{then}\\," (print-term then (sub1 depth)) "\\\\"
         "\\mathtt{else}\\," (print-term else (sub1 depth))
         "\\end{array}\\right)")]
       [(ECAbs ec ec-lower ec-upper body)
        (string-append "\\left( \\Lambda "
                       (print-bounds ec ec-lower ec-upper) ".\\,"
                       (print-term body (sub1 depth))
                       "\\right)")]
       [(ECAbsCC α body)
        (string-append "\\left( \\Lambda "
                       (id->string α) ".\\,"
                       (print-term body (sub1 depth))
                       "\\right)")]
       [(ECApp term ec)
        (string-append (print-term term (sub1 depth)) "[" (print-ec ec) "]")]
       [(ECAppℓ term ec ℓ)
        (string-append (print-term term (sub1 depth)) "[" (print-ec ec) "]")]
       [(ECSubIntro sub-ec sup-ec body)
        (string-append "\\left( "
                       (print-ec sub-ec) " <: " (print-ec sup-ec) "\\Rightarrow\\,"
                       (print-term body (sub1 depth))
                       "\\right)")]
       [(ECSubElim term)
        (string-append (print-term term (sub1 depth)) "\\,\\bullet")]
       [(ECSubElimDyn term label)
        (string-append (print-term term (sub1 depth)) "\\,\\bullet\\star")]
       [(or (Ref term) (RefAnn term _))
        (string-append "\\mathsf{ref} " (print-term term (sub1 depth)))]
       [(Set ref rhs)
        (string-append (print-term ref (sub1 depth)) " := " (print-term rhs (sub1 depth)))]
       [(Setℓ ref rhs ℓ)
        (string-append (print-term ref (sub1 depth)) " := " (print-term rhs (sub1 depth)))]
       [(Deref term)
        (string-append "!" (print-term term (sub1 depth)))]
       [(Derefℓ term ℓ)
        (string-append "!" (print-term term (sub1 depth)))]
       [(Quote obj-term ec)
        (string-append "\\quot{" (print-term obj-term (sub1 depth)) "}"
                       "^{" (print-ec ec) "}")]
       [(Cast term coer)
        (string-append "\\begin{array}{l}" (print-term term (sub1 depth)) "\\\\"
                       "\\langle" (print-coercion coer) "\\rangle"
                       "\\end{array}")]
       [(Blame A label)
        (string-append "\\mathtt{blame}\\," (print-type A) " " (print-label label))]
       [(Asc M A)
        (string-append (print-term M (sub1 depth)) " : " (print-type A))]
       [(Loc a)
        (string-append "\\mathtt{@}\\{" (~a a) "\\}")]
       [(Prim args-t ret-t fun name) (string-append  "\\mathtt{" (symbol->string name) "}")]
            )]))

(define (print-coercion c [depth (print-depth)])
  (match c
    [(CId (ECVar α))
     (string-append "\\mathtt{id}_{" (print-ec (ECVar α)) "}")]
    [(CId (ECEps))
     (string-append "\\mathtt{id}_{" (print-ec (ECEps)) "}")]
    [(CId A)
     (string-append "\\mathtt{id}_{" (print-type A) "}")]
    [(CInj (ECVar α)) (string-append (print-ec (ECVar α)) "!")]
    [(CInj (ECEps)) (string-append (print-ec (ECEps)) "!")]
    [(CInj G) (string-append (print-type G) "!")]
    [(CProj (ECVar α) label) (string-append (print-ec (ECVar α)) "?")]
    [(CProj (ECEps) label) (string-append (print-ec (ECEps)) "?")]
    [(CProj G label) (string-append (print-type G) "?")]
    [(CFun c d)
     (string-append "(" (print-coercion c (sub1 depth)) "\\to" (print-coercion d (sub1 depth)) ")")]
    [(CECUniv X p)
     (string-append "(\\forall\\," (id->string X)
                    ".\\," (print-coercion p (sub1 depth)) ")")]
    [(CECSub sub-ec sup-ec body)
     (string-append "( " (print-ec sub-ec) " <: " (print-ec sup-ec) "\\Rightarrow\\,"
                    (print-coercion body (sub1 depth)) ")")]
    [(CCode c ec)
     (string-append "\\quot{" (print-coercion c (sub1 depth)) "}"
                    "^{" (print-coercion ec (sub1 depth)) "}")]
    [(CHyp h m t)
     (string-append "\\left(" (print-coercion h (sub1 depth)) ";"
                    (print-coercion m (sub1 depth)) ";"
                    (print-coercion t (sub1 depth)) "\\right)")]
    [(CRefT c d)
     (string-append "\\mathtt{Ref}\\," (print-coercion c (sub1 depth)) "\\," (print-coercion d (sub1 depth)))]
    [(CSub low hi)
     (string-append (print-ec low) " \\uparrow " (print-ec hi))]
    [(CBot A B label)
     (string-append "\\bot_{" (print-type A) "\\Rightarrow" (print-type B) "}" (print-label label))]
    [else (error 'print-coercion "unmatched ~a" c)]
    ))


(define (term-ec-rename term β new-ec)
  (define (recurse trm)
    (term-ec-rename trm β new-ec))
  (match term
    [(or (? Const?) (? Prim?) (? Loc?))
     term]
    [(App L M)
     (App (recurse L) (recurse M))]
    [(AppAnn L M A)
     (AppAnn (recurse L) (recurse M) (type-ec-rename A β new-ec))]
    [(Appℓ L M ℓ)
     (Appℓ (recurse L) (recurse M) ℓ)]
    [(OVar x) (OVar x)]
    [(MVar x) (MVar x)]
    [(OFixAbs α f γ x A B M)
     (define A′ (type-ec-rename A β new-ec))
     (define B′ (type-ec-rename B β new-ec))
     (define α′ (gen-id α))
     (define γ′ (gen-id γ))
     (define new-M (term-ec-rename (term-ec-rename M α (ECVar α′)) γ (ECVar γ′)))
     (OFixAbs α′ f γ′ x A′ B′ (recurse new-M))]
    [(OFixAbsVal α f γ x A B M) ;; α, f, γ, x are not binders
     (define A′ (type-ec-rename A β new-ec))
     (define B′ (type-ec-rename B β new-ec))
     (OFixAbsVal α f γ x A′ B′ (recurse M))]
    [(OAbs α x A M)
     (define A′ (type-ec-rename A β new-ec))
     (define α′ (gen-id α))
     (define new-M (term-ec-rename M α (ECVar α′)))
     (OAbs α′ x A′ (recurse new-M))]
    [(MFixAbs f x A B M)
     (define A′ (type-ec-rename A β new-ec))
     (define B′ (type-ec-rename B β new-ec))
     (MFixAbs f x A′ B′ (recurse M))]
    [(MFixAbsℓ f x A B M ℓ)
     (define A′ (type-ec-rename A β new-ec))
     (define B′ (type-ec-rename B β new-ec))
     (MFixAbsℓ f x A′ B′ (recurse M) ℓ)]
    [(MAbs x A M)
     (define A′ (type-ec-rename A β new-ec))
     (MAbs x A′ (recurse M))]
    [(Splice N)
     (Splice (recurse N))]
    [(Spliceℓ N ℓ)
     (Spliceℓ (recurse N) ℓ)]
    [(If test then else)
     (If (recurse test) (recurse then) (recurse else))]
    [(IfAnn test then else A)
     (IfAnn (recurse test) (recurse then) (recurse else) (type-ec-rename A β new-ec))]
    [(Ifℓ test then else ℓ)
     (Ifℓ (recurse test) (recurse then) (recurse else) ℓ)]
    [(ECAbsCC α body)
     (define α′ (gen-id α))
     (define new-body (term-ec-rename body α (ECVar α′)))
     (ECAbsCC α′ (recurse new-body))]
    [(ECApp term ec)
     (ECApp (recurse term) (ec-rename ec β new-ec))]
    [(ECAppℓ term ec ℓ)
     (ECAppℓ (recurse term) (ec-rename ec β new-ec) ℓ)]
    [(ECSubIntro sub-ec sup-ec body)
     (define sub-ec′ (ec-rename sub-ec β new-ec))
     (define sup-ec′ (ec-rename sup-ec β new-ec))
     (ECSubIntro sub-ec′ sup-ec′ (recurse body))]
    [(ECSubElim term)
     (ECSubElim (recurse term))]
    [(ECSubElimDyn term label)
     (ECSubElimDyn (recurse term) label)]
    [(RefAnn term type)
     (RefAnn (recurse term) (type-ec-rename type β new-ec))]
    [(Set ref rhs)
     (Set (recurse ref) (recurse rhs))]
    [(Setℓ ref rhs ℓ)
     (Setℓ (recurse ref) (recurse rhs) ℓ)]
    [(Deref term)
     (Deref (recurse term))]
    [(Derefℓ term ℓ)
     (Derefℓ (recurse term) ℓ)]
    [(Quote obj-term ec)
     (Quote (recurse obj-term) (ec-rename ec β new-ec))]
    [(Cast term coer)
     (Cast (recurse term) (coerce-rename-ec coer β new-ec))]
    [(Blame A label)
     (Blame (type-ec-rename A β new-ec) label)]
    [(Asc M A)
     (Asc (recurse M) (type-ec-rename A β new-ec))]
    [else (error 'term-ec-rename "unmatched ~a" term)]
    ))

(define (coerce-rename-ec coer β new-ec)
  (define (recurse trm)
    (coerce-rename-ec trm β new-ec))
  (match coer
     [(CId A)    (CId (type-ec-rename A β new-ec))]
     [(CInj G)   (CInj (type-ec-rename G β new-ec))]
     [(CProj G label)  (CProj (type-ec-rename G β new-ec) label)]
     [(CFun c d) (CFun (recurse c) (recurse d))]
     [(CECUniv α c)
     (define α′ (gen-id α))
     (define new-c (coerce-rename-ec c α (ECVar α′)))
     (CECUniv α′ (recurse new-c))]
     [(CECSub sub-ec sup-ec c)
      (define sub-ec^ (ec-rename sub-ec β new-ec))
      (define sup-ec^ (ec-rename sup-ec β new-ec))
      (CECSub sub-ec^ sup-ec^ (recurse c))]
     [(CCode c ce)
      (CCode (recurse c) (ec-coerce-rename-ec ce β new-ec))]
     [(CHyp h m t)
      (CHyp (recurse h) (recurse m) (recurse t))]
     [(CRefT c d)
      (CRefT (recurse c) (recurse d))]
     [(CBot A B label)
      (CBot (type-ec-rename A β new-ec) (type-ec-rename B β new-ec) label)]
     [else (error 'coerce-rename-ec "unmatched ~a" coer)]
     ))

(define (ec-coerce-rename-ec coer β new-ec)
  (define (recurse c)
    (ec-coerce-rename-ec c β new-ec))
  (match coer
     [(CId ec)    (CId (ec-rename ec β new-ec))]
     [(CInj ec)   (CInj (ec-rename ec β new-ec))]
     [(CProj ec label)  (CProj (ec-rename ec β new-ec) label)]
     [(CSub ec1 ec2)
      (CSub (ec-rename ec1 β new-ec)
            (ec-rename ec2 β new-ec))]
     [(CHyp h m t)
      (CHyp (recurse h) (recurse m) (recurse t))]
    [(CBot ec1 ec2 label)
     (CBot (ec-rename ec1 β new-ec) (ec-rename ec2 β new-ec) label)]
    [else (error 'ec-coerce-rename-ec "unmatched ~a" coer)]
    ))

(define (term-subst term var new-term)
  (define (recurse trm)
    (term-subst trm var new-term))
  (match term
    [(or (? Const?) (? Prim?) (? Loc?))
     term]
    [(App L M)
     (App (recurse L) (recurse M))]
    [(AppAnn L M A)
     (AppAnn (recurse L) (recurse M) A)]
    [(OVar x)
     (cond [(equal? x var) new-term]
           [else (OVar x)])]
    [(MVar x)
     (cond [(equal? x var) new-term]
           [else (MVar x)])]
    [(OFixAbs α f β x A B M)
     (define α′ (gen-id α))
     (define f′ (gen-id f))
     (define β′ (gen-id β))
     (define x′ (gen-id x))
     (define new-M (term-subst (term-ec-rename (term-subst (term-ec-rename
                                                            M α (ECVar α′))
                                                           f (OVar f′))
                                               β (ECVar β′))
                               x (OVar x′)))
     (OFixAbs α′ f′ β′ x′ A B (recurse new-M))]
    [(OFixAbsVal α f β x A B M) ;; α, f, β, x are not binders
     (OFixAbsVal α f β x A B (recurse M))]
    [(MFixAbs f x A B M)
     (define f′ (gen-id f))
     (define x′ (gen-id x))
     (define new-M (term-subst (term-subst M f (MVar f′)) x (MVar x′)))
     (MFixAbs f′ x′ A B (recurse new-M))]
    [(Splice N)
     (Splice (recurse N))]
    [(IfAnn test then else A)
     (IfAnn (recurse test) (recurse then) (recurse else) A)]
    [(ECAbsCC α body)
     (define α′ (gen-id α))
     (define new-body (term-ec-rename (recurse body) α (ECVar α′)))
     (ECAbsCC α′ new-body)]
    [(ECApp term ec)
     (ECApp (recurse term) ec)]
    [(ECSubIntro sub-ec sup-ec body)
     (ECSubIntro sub-ec sup-ec (recurse body))]
    [(ECSubElim term)
     (ECSubElim (recurse term))]
    [(ECSubElimDyn term label)
     (ECSubElimDyn (recurse term) label)]
    [(RefAnn term A)
     (RefAnn (recurse term) A)]
    [(Set ref rhs)
     (Set (recurse ref) (recurse rhs))]
    [(Deref term)
     (Deref (recurse term))]
    [(Quote obj-term ec)
     (Quote (recurse obj-term) ec)]
    [(Cast term coer)
     (Cast (recurse term) coer)]
    [(Blame A label)
     (Blame A label)]
    [(Asc M A)
     (Asc (recurse M) A)]
    [else (error 'term-subst "unmatched ~a" term)]
    ))

;; (require racket/trace)
;; (trace term-ec-rename)
