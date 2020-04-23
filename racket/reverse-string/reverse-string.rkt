#lang racket
(provide my-reverse)

(define (my-reverse s)
  (list->string (reverse (string->list s))))
