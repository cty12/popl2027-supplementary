#lang racket

(provide define-log-topic log with-log-topics debug)

(define-syntax-rule (define-log-topic topic)
  (define topic (make-parameter #f)))

(define-syntax-rule (log topic msg fmt-args ...)
  (when (topic)
    (apply printf `(,(string-append msg "~n")  ,fmt-args ...))))

(define-syntax-rule (with-log-topics (topics ...) body ...)
  (parameterize ([topics #t] ...) body ...))

(define-log-topic debug)
