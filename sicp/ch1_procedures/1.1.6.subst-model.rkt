#lang sicp
;; Exercise 1.3: Define a procedure that takes three numbers
;; as arguments and returns the sum of the squares of the two
;; larger numbers.

(define (sum-squares a b)
  (+ (* a a) (* b b)))

(define (sum-squares-of-two-greatest a b c)
  (cond ((and (<= a b) (<= a c)) (sum-squares b c))
        ((<= b c) (sum-squares a c))
        (else (sum-squares a b))))

(= 13 (sum-squares-of-two-greatest 1 2 3))
(= 10 (sum-squares-of-two-greatest 1 -2 3))
(= 5 (sum-squares-of-two-greatest -1 -2 -3))
