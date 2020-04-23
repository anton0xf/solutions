#lang racket
(provide to-roman)

(define base
  '(("I" . 1)
    ("IV" . 4) ("V" . 5) ("IX" . 9) ("X" . 10)
    ("XL" . 40) ("L" . 50) ("XC" . 90) ("C" . 100)
    ("CD" . 400) ("D" . 500) ("CM" . 900) ("M" . 1000)))

(define (to-roman n)
  (define nums (reverse (map car base)))
  (define values (make-immutable-hash base))
  (define (value num) (hash-ref values num))
  (define (iter n nums acc)
    (let* ([num (first nums)]
           [v (value num)])
      (cond [(zero? n) acc]
            [(>= n v) (iter (- n v) nums (cons num acc))]
            [else (iter n (rest nums) acc)])))
  (string-join (reverse (iter n nums '())) ""))
