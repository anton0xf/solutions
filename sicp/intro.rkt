#lang sicp
(exact->inexact (/ 5 2))
(define three (+ 1 2))
three

(define (abs x)
  (cond ((< x 0) (- x))
        (else x)))



