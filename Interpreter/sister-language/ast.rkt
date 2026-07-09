#lang racket
(require "logging.rkt")

(provide (all-defined-out))

;; Common types
(struct Base (name) #:transparent)
(struct Fun (dom codom) #:transparent)

;; Environment Classifier Expressions
(struct ECVar (name) #:transparent)
(struct ECEps () #:transparent)

;; Meta language types
(struct RefT (type) #:transparent)
(struct Code (type ec) #:transparent)
(struct ECUniv (param-ec ec-lower ec-upper body) #:transparent)

;; Common terms
(struct Const (name) #:transparent)
(struct App (rator rand) #:transparent)
(struct If (test then else) #:transparent)

;; Meta language terms
(struct MVar (name) #:transparent)
(struct MAbs (param param-t body) #:transparent)
(struct MFixAbs (rec-param param param-t return-t body) #:transparent)
(struct ECAbs (ec-param ec-lower ec-upper body) #:transparent)
(struct ECApp (term ec) #:transparent)
(struct Ref (term) #:transparent)
(struct Set (ref rhs) #:transparent)
(struct Deref (term) #:transparent)
(struct Quote (obj-term ec) #:transparent)

;; Object language terms
(struct Asc (term type) #:transparent) ; type ascription
(struct OVar (name) #:transparent)
(struct OAbs (ec-param param param-t body) #:transparent)
(struct OFixAbs (ec-param rec-param param param-t return-t body) #:transparent)
(struct Splice (term) #:transparent)

;; This predicate checks whether all the splices are gone.
(define (stlc-term? ast)
  (match ast
    [(OVar name) #t]
    [(OAbs ec-param param param-t body)
     (stlc-term? body)]
    [(OFixAbs ec-param rec-param param param-t return-t body)
     (stlc-term? body)]
    [(Const c) #t]
    [(App rator rand) (and (stlc-term? rator) (stlc-term? rand))]
    [(If test then else)
     (and (stlc-term? test) (stlc-term? then) (stlc-term? else))]
    [_ #f]))

;; precondition: (and (meta-type? A) (meta-type? B))
(define (meta-type-α-equiv? A B [scope1 '()] [scope2 '()])
  (define (recurse A^ B^)
    (meta-type-α-equiv? A^ B^ scope1 scope2))
  (match* (A B)
    [((Base name1) (Base name2)) (equal? name1 name2)]
    [((Fun dom1 codom1) (Fun dom2 codom2))
     (and (recurse dom1 dom2)
          (recurse codom1 codom2))]
    [((RefT type1) (RefT type2))
     (recurse type1 type2)]
    [((Code type1 ec1) (Code type2 ec2))
     (define ec1-pos (index-of scope1 ec1))
     (define ec2-pos (index-of scope2 ec2))
     (cond
       [(not (equal? ec1-pos ec2-pos))
        (meta-type-α-equiv?-log 'code A B ec1-pos ec2-pos)
        #f]
       [else (equal? type1 type2)])]
    [((ECUniv α ec-lower1 ec-upper1 body1)
      (ECUniv β ec-lower2 ec-upper2 body2))
     (define ec1-upper-pos (index-of scope1 ec-upper1))
     (define ec2-upper-pos (index-of scope2 ec-upper2))
     (define ec1-lower-pos (index-of scope1 ec-lower1))
     (define ec2-lower-pos (index-of scope2 ec-lower2))
     (cond
       [(not (equal? ec1-upper-pos ec2-upper-pos))
        (meta-type-α-equiv?-log 'ec-univ-upper A B ec1-upper-pos ec2-upper-pos)
        #f]
       [(not (equal? ec1-lower-pos ec2-lower-pos))
        (meta-type-α-equiv?-log 'ec-univ-lower A B ec1-lower-pos ec2-lower-pos)
        #f]
       [else (meta-type-α-equiv? body1 body2
                                 (cons (ECVar α) scope1)
                                 (cons (ECVar β) scope2))])]
    [(_ _)
     (log debug "Not α-equivalent types:~n~v~n~v" A B)
     #f]))

(define (meta-type-α-equiv?-log key A B ec1-pos ec2-pos)
  (match key
    ['code
     (log debug
          (string-append
           "The code types ~a and ~a are not α-equivalent because "
           "the env classifier in the first code type is bound to "
           "a binder at position ~a while the classifier in the "
           "second code type is bound to a binder at position ~a")
          A B ec1-pos ec2-pos)]
    ['ec-univ-upper
     (log debug
          (string-append
           "The universal types ~a and ~a are not α-equivalent because "
           "the env classifier upper bound in the first universal type is bound to "
           "a binder at position ~a while the classifier bound in the "
           "second universal type is bound to a binder at position ~a")
          A B ec1-pos ec2-pos)]
    ['ec-univ-lower
     (log debug
          (string-append
           "The universal types ~a and ~a are not α-equivalent because "
           "the env classifier lower bound in the first universal type is bound to "
           "a binder at position ~a while the classifier bound in the "
           "second universal type is bound to a binder at position ~a")
          A B ec1-pos ec2-pos)]
    [_ (error 'meta-type-α-equiv?-log "Invalid error key: ~a" key)]))

;; precondition: (and (object-term? M) (object-term? N))
(define (object-term-α-equiv? M N [scope1 '()] [scope2 '()])
  (match* (M N)
    [((OVar name1) (OVar name2))
     #:when (equal? (index-of scope1 M) (index-of scope2 N))
     #t]
    [((OAbs α param1 param-t1 body1)
      (OAbs β param2 param-t2 body2))
     (and (equal? param-t1 param-t2)
          (object-term-α-equiv? body1 body2
                                (cons (ECVar α) (cons (OVar param1) scope1))
                                (cons (ECVar β) (cons (OVar param2) scope2))))]
    [((OFixAbs α rec-param1 param1 param-t1 return-type1 body1)
      (OFixAbs β rec-param2 param2 param-t2 return-type2 body2))
     (and (equal? param-t1 param-t2)
          (equal? return-type1 return-type2)
          (object-term-α-equiv? body1 body2
                                (cons (ECVar α) (cons (OVar param1) scope1))
                                (cons (ECVar β) (cons (OVar param2) scope2))))]
    [((Splice term1) (Splice term2)) #f]
    [(_ _) (*-term-α-equiv? object-term-α-equiv? M N scope1 scope2)]))

(define (*-term-α-equiv? self M N scope1 scope2)
  (define (recurse t1 t2)
    (self t1 t2 scope1 scope2))
  (match* (M N)
    [((Const c1) (Const c2)) (equal? c1 c2)]
    [((App rator1 rand1) (App rator2 rand2))
     (and (recurse rator1 rator2)
          (recurse rand1 rand2))]
    [((If test1 then1 else1) (If test2 then2 else2))
     (and (recurse test1 test2) (recurse then1 then2) (recurse else1 else2))]
    [(_ _)
     (log debug "Not α-equivalent terms:~n~v~n~v" M N)
     #f]))

(define (ec-var-rename α β new-ec)
  (match new-ec
    [(ECVar γ)
     (cond [(equal? α β)  γ]
           [else          α])]
    [else
     (error 'ec-var-rename "can't rename to ~a" new-ec)]))
  
(define (ec-rename ec β new-ec)
  (match ec
    [(ECVar α)
     (cond [(equal? α β)
            new-ec]
           [else (ECVar α)])]
    [_ ec]))

;; TODO: Fix error messages so that long terms being printed are on new lines
;; TODO: print unparsed terms and nested structs using ~v instead of ~a
(define (type-ec-rename type β new-ec)
  (type-ec-rename^ type-ec-rename type β new-ec))

(define (type-ec-rename^ self type β new-ec)
  (define (recurse t) (self t β new-ec))
  (match type
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
