#lang racket

(provide leap-year?)

(define (leap-year? year)
  (define (divisible-by? m)
    (zero? (remainder year m)))
  (if (divisible-by? 100)
      (divisible-by? 400)
      (divisible-by? 4)))
