#lang racket
(require math)

(provide classify)

(define (classify n)
  (define aliquot-sum
    (sum (drop-right (divisors n) 1))) 
  (cond [(= n aliquot-sum) 'perfect]
        [(< n aliquot-sum) 'abundant]
        [else 'deficient]))
