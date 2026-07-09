#lang racket

(require graph)
(require rackunit)
(require "../ast.rkt")
(require "../parse.rkt")
(require "../typecheck.rkt")

(define ctx
  (hasheqv
   'x (MType (Base 'Bool))
   'α (EC)
   'y (OType (Fun (Base 'Int) (Base 'Int)) 'α)
   'β (EC)
   'w (OType (RefT (Base 'Int)) 'β)
   'z (MType (RefT (Fun (Base 'Str) (Base 'Str))))))

(check-true (well-formed-ec? (ECVar 'α) ctx))
(check-true (well-formed-ec? (ECVar 'β) ctx))
(check-false (well-formed-ec? (ECVar '⊤) ctx))
(check-true (well-formed-ec? (ECEps) ctx))
(check-false (well-formed-ec? (ECVar 'γ) ctx))

(check-true (well-formed-meta-type?
             (parse-meta-type
              '(→ (∀̇ (_ <: α <: _) (→ (Ref Int) (‶ Bool ″ α))) (‶ Int ″ ε)))))
(check-false (well-formed-meta-type? (Code (Base 'Int) (ECVar 'α))))
(check-false (well-formed-meta-type? (ECUniv 'α (ECEps) (ECVar 'β) (Code (Base 'Int) (ECVar 'α)))))
(check-false (well-formed-meta-type? (ECUniv 'α (ECEps) #f
                                             (ECUniv 'α (ECEps) #f
                                                     (Code (Base 'Int) (ECVar 'α))))))

(define ec-subtypes
  (unweighted-graph/directed
   '((α β) (α β^) (β α^) (β^ α^) (α^ α^^))))

(check-true (ec-<: (ECVar 'α) (ECVar 'β) ec-subtypes))
(check-true (ec-<: (ECVar 'α) (ECVar 'α) ec-subtypes))
(check-true (ec-<: (ECVar 'β) (ECVar 'β) ec-subtypes))
(check-false (ec-<: (ECVar 'β) (ECVar 'α) ec-subtypes))
(check-false (ec-<: (ECVar 'α) (ECVar 'γ) ec-subtypes))
(check-false (ec-<: (ECVar 'γ) (ECVar 'β) ec-subtypes))
(check-true (ec-<: (ECVar 'γ) (ECVar 'γ) ec-subtypes))
(check-true (ec-<: (ECVar 'α) (ECVar 'α^) ec-subtypes))
(check-true (ec-<: (ECVar 'α) (ECVar 'α^^) ec-subtypes))

(check-true
 (meta-type-<:
  (parse-meta-type '(∀̇ (_ <: α <: _)
                       (∀̇ (_ <: β <: α)
                          (→ (Ref (‶ Int ″ α)) (‶ Bool ″ β)))))
  (parse-meta-type '(∀̇ (_ <: α^ <: _)
                       (∀̇ (_ <: β^ <: α^)
                          (→ (Ref (‶ Int ″ α^)) (‶ Bool ″ α^)))))))
(check-true
 (meta-type-<:
  (parse-meta-type '(∀̇ (_ <: α <: _)
                       (∀̇ (_ <: β <: α)
                          (→ (Ref (‶ Int ″ α)) (‶ Bool ″ β)))))
  (parse-meta-type '(∀̇ (_ <: α^ <: _)
                       (∀̇ (_ <: β^ <: α^)
                          (→ (Ref (‶ Int ″ α^)) (‶ Bool ″ β^)))))))
(check-true
 (meta-type-<:
  (parse-meta-type '(∀̇ (_ <: α <: _)
                       (∀̇ (_ <: β <: α)
                          (→ (Ref (‶ Int ″ α)) (‶ Bool ″ β)))))
  (parse-meta-type '(∀̇ (_ <: α^ <: _)
                       (∀̇ (_ <: β^ <: α^)
                          (→ (Ref (‶ Int ″ α^)) (‶ Bool ″ β^)))))))
;; Arguments of Ref types should be α-equiv
(check-false
 (meta-type-<:
  (parse-meta-type '(∀̇ (_ <: α <: _)
                       (∀̇ (_ <: β <: α)
                          (→ (Ref (‶ Int ″ α)) (‶ Bool ″ β)))))
  (parse-meta-type '(∀̇ (_ <: α^ <: _)
                       (∀̇ (_ <: β^ <: α^)
                          (→ (Ref (‶ Int ″ β^)) (‶ Bool ″ β^)))))))
;; ECs used in Code types should be subtypes
(check-false
 (meta-type-<:
  (parse-meta-type '(∀̇ (_ <: α <: _)
                       (∀̇ (_ <: β <: α)
                          (→ (Ref (‶ Int ″ α)) (‶ Bool ″ α)))))
  (parse-meta-type '(∀̇ (_ <: α^ <: _)
                       (∀̇ (_ <: β^ <: α^)
                          (→ (Ref (‶ Int ″ α^)) (‶ Bool ″ β^)))))))

(check-equal? (ec-⨆ (ECVar 'α) (ECVar 'β) ec-subtypes) (ECVar 'β))
(check-equal? (ec-⨆ (ECVar 'α) (ECVar 'α^) ec-subtypes) (ECVar 'α^))
(check-equal? (ec-⨅ (ECVar 'α) (ECVar 'β) ec-subtypes) (ECVar 'α))

(define (ecs-from-subtypes subtypes)
  (cons (ECEps) (map ECVar (get-vertices subtypes))))

(define-check (check-⨆ ec1 ec2 subtypes)
  (define ec3 (ec-⨆ ec1 ec2 subtypes))
  (unless (ec-<: ec1 ec3 subtypes)
    (fail-check (format
                 "The least upper bound ~a of ~a and ~a should be a supertype of ~a"
                 ec3 ec1 ec2 ec1)))
  (unless (ec-<: ec2 ec3 subtypes)
    (fail-check (format
                 "The least upper bound ~a of ~a and ~a should be a supertype of ~a"
                 ec3 ec1 ec2 ec2)))
  (define ecs (ecs-from-subtypes subtypes))
  (for ([ec (in-list ecs)]
        #:when (and (ec-<: ec1 ec subtypes)
                    (ec-<: ec2 ec subtypes)))
    (unless (ec-<: ec3 ec subtypes)
      (fail-check (format
                   (string-append
                    "The least upper bound ~a of ~a and ~a should be a subtype "
                    "of another upper bound ~a")
                   ec3 ec1 ec2 ec)))))

(define-check (check-⨅ ec1 ec2 subtypes)
  (define ec3 (ec-⨅ ec1 ec2 subtypes))
  (unless (ec-<: ec3 ec1 subtypes)
    (fail-check (format
                 "The greatest lower bound ~a of ~a and ~a should be a subtype of ~a"
                 ec3 ec1 ec2 ec1)))
  (unless (ec-<: ec3 ec2 subtypes)
    (fail-check (format
                 "The greatest lower bound ~a of ~a and ~a should be a subtype of ~a"
                 ec3 ec1 ec2 ec2)))
  (define ecs (ecs-from-subtypes subtypes))
  (for ([ec (in-list ecs)]
        #:when (and (ec-<: ec ec1 subtypes)
                    (ec-<: ec ec2 subtypes)))
    (unless (ec-<: ec ec3 subtypes)
      (fail-check (format
                   (string-append
                    "The greatest lower bound ~a of ~a and ~a should be a supertype "
                    "of another lower bound ~a"))
                  ec3 ec1 ec2 ec))))

(for* ([ec1 (ecs-from-subtypes ec-subtypes)]
       [ec2 (ecs-from-subtypes ec-subtypes)])
  (check-⨆ ec1 ec2 ec-subtypes)
  (check-⨅ ec1 ec2 ec-subtypes))

;; TODO: add negative test cases which trigger exceptions not related to STLC

