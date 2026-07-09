#lang racket

(require racket/exn)
(require "ast.rkt")
(require "parse.rkt")
(require "stepper.rkt")
(require "sister-language/tools.rkt")
(require "sister-language/logging.rkt")

(define (run-test test-prog-path)
  (define tex-file (path-replace-extension test-prog-path ".tex"))
  (define res-file (path-replace-extension test-prog-path ".res"))
  (define err-file (path-replace-extension test-prog-path ".err"))
  (define test-pass 1)
  (define test-fail 0)
  (define term-ast (read-term test-prog-path))
  (cond
    [(file-exists? err-file)
     (log debug "Checking error for ~a" test-prog-path)
     (define expected-error-regexp
       (regexp (call-with-input-file err-file
                 (λ (f)
                   (string-trim (port->string f))))))
     (with-handlers ([(exn:fail-match? expected-error-regexp)
                      (λ (e)
                        (log debug "Test passed for ~a" test-prog-path)
                        test-pass)]
                     [exn:fail?
                      (λ (e)
                        (log debug "Test failed for ~a" test-prog-path)
                        (log debug "Expected error message matching ~a but got the following error:~n~a~n"
                             expected-error-regexp
                             (exn->string e))
                        test-fail)])
       (run term-ast tex-file)
       (log debug "Test failed for ~a" test-prog-path)
       (log debug "Expected error message matching '~a' but got no error" expected-error-regexp)
       test-fail)]
    [else
     (log debug "Checking result for ~a" test-prog-path)
     (define expected-val
       (if (file-exists? res-file) (read-term res-file)
           (Const 42)))
     (with-handlers ([exn:fail?
                      (λ (e)
                        (log debug "Test failed for ~a" test-prog-path)
                        (log debug "Expected no errors but got the following error:~n~a~n"
                             (exn->string e))
                        test-fail)])
       (define actual-val (run term-ast tex-file))
       (cond
         [(equal? actual-val expected-val)
          (log debug "Test passed for ~a" test-prog-path)
          test-pass]
         [else
          (log debug "Test failed for ~a" test-prog-path)
          (log debug "Expected and actual values don't match:~nActual value:~n~a~nExpected value:~n~a~n"
               actual-val expected-val)
          test-fail]))]))

(define ((exn:fail-match? regexpr) e)
  (and (exn:fail? e) (regexp-match regexpr (exn->string e))))

(debug #f)

(programs-directory "./examples")
(define gradual-examples (list-programs ".lar"))
(programs-directory "sister-language/examples/")
(define static-examples (list-programs ".lar"))
(define all-examples (append gradual-examples static-examples))

(define-values (tests-passed total-tests)
  (for/fold
    ([tests-passed 0] [total-tests 0])
    ([prog-file #;'("./examples/scope-extrusion-higher-order.lar"
                  "sister-language/examples/power.lar"
                  "sister-language/examples/power-simple.lar")
                all-examples])
    (log debug "------------Testing start for ~a------------" prog-file)
    (define test-passed (run-test prog-file))
    (log debug "------------Testing end for ~a------------~n" prog-file)
    (values (+ tests-passed test-passed) (+ total-tests 1))))

(printf "~a/~a tests succeeded~a~n"
         tests-passed total-tests
         (if (debug) "" " (enable debug to see details)"))

