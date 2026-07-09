#lang racket

(require rackunit)
(require "../parse.rkt")
(require "../typecheck.rkt")
(require "../evaluate.rkt")
(require "../tools.rkt")
(require "../logging.rkt")

(debug #f)
(programs-directory "../examples")
(for ([prog-file #;`(,(build-path (programs-directory) "code-type-check-err.lar"))
                 (list-programs ".lar")])
  (define type-file (path-replace-extension prog-file ".type"))
  (define type-err-file (path-replace-extension prog-file ".tyerr"))
  (define result-file (path-replace-extension prog-file ".res"))
  (cond
    [(file-exists? type-file)
     (log debug "Checking result of ~a" prog-file)
     (check-equal? (meta-typecheck (read-term prog-file)) (read-type type-file))
     (unless (file-exists? result-file)
       (error 'test-examples
              (string-append
               "Well typed program ~a whose type is in ~a should have "
               "a corresponding .res file")
              prog-file type-file))
     (check-full-eval-equiv? (read-term prog-file) (read-term result-file))]
    [(file-exists? type-err-file)
     (log debug "Checking error of ~a" prog-file)
     (check-exn (regexp (call-with-input-file type-err-file
                          (λ (f)
                            (string-trim (port->string f)))))
                (λ ()
                  (meta-typecheck (read-term prog-file))))]
    [else
     (error
      'typecheck-test
      "The program file ~a should either have a corresponding .type or .tyerr file"
      prog-file)]))

