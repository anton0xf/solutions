#lang racket
(provide rebase)

(define (valid-base? base) (< 1 base))

(define (valid-digit? d base)
  (and (not (negative? d))
       (< d base)))

(define (digits->number digits-list base)
  (foldl (λ (d acc) (+ d (* acc base)))
         0 digits-list))

(define (number->digits n base)
  (define (iter n acc)
    (if (zero? n) acc
        (iter (quotient n base)
              (cons (remainder n base) acc))))
  (if (zero? n) '(0)
      (iter n '())))

(define (rebase digits-list in-base out-base)
  (and (valid-base? in-base)
       (valid-base? out-base)
       (andmap (λ (d) (valid-digit? d in-base)) digits-list)
       (number->digits (digits->number digits-list in-base)
                       out-base)))
