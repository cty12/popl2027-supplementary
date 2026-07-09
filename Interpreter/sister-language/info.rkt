#lang info

(define collection "glar")
(define deps '("base" "rackunit"))
(define build-deps '("rackunit-lib"))
(define pkg-desc
  "Impementation for Gradual Lambda Alpha Ref: a metaprogramming language with mutable references")
(define version "0.1")
(define test-omit-paths '())
(define test-include-paths '("tests/ast.rkt" "tests/parse.rkt"))
(define license 'MIT)
