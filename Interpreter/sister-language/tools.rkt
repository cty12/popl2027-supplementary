#lang racket

(provide read-program
         read-program-syntax
         programs-directory
         list-programs)

(define ((read-program abstractify-program) path)
  (unless (or (string? path) (path? path))
    (error 'read-program "expected a string in ~s" path))
  (unless (file-exists? path)
    (error 'read-program "file doesn't exist in ~s" path))
  (define input-prog
    (call-with-input-file path
      (lambda (f)
        `(program () ,@(for/list ([e (in-port read f)]) e)))))
  (define ast (abstractify-program input-prog))
  ast)

(define ((read-program-syntax abstractify-program) path)
  (unless (or (string? path) (path? path))
    (error 'read-program "expected a string in ~s" path))
  (unless (file-exists? path)
    (error 'read-program "file doesn't exist in ~s" path))
  (define input-prog
    (parameterize ([port-count-lines-enabled #t])
      (call-with-input-file path
      (lambda (f)
        #`(program
           ()
           #,@(for/list ([e (in-port (λ (in) (read-syntax path in)) f)])
                e))))))
  (define ast (abstractify-program input-prog))
  ast)

(define programs-directory
  (make-parameter
   (build-path ".")
   (λ (v)
     (unless (and (path-string? v)
                  (directory-exists? v))
       (error 'programs-directory-exists
              "Expected new programs-directory to be an existing directory, but got ~a"
              v))
     v)))

(define (list-programs [ext #f])
  (for/list ([f (directory-list (programs-directory))]
             #:do [(define p (build-path (programs-directory) f))]
             #:when (and (equal? (file-or-directory-type p) 'file)
                         (if ext (path-has-extension? p ext) #t)))
    p))
