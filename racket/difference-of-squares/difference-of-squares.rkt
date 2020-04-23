#lang racket

(provide sum-of-squares square-of-sum difference)

(define (sum-of-squares n)
  ;; n * (n + 1) * (2*n + 1) / 6
  (* 1/6 n (add1 n)
     (add1 (* 2 n))))

(define (square-of-sum n)
  (expt (* n (add1 n) 1/2)
        2))

(define (difference n)
  (- (square-of-sum n)
     (sum-of-squares n)))
