#lang racket

(provide to-roman)

(define roman-digits
  '((#\I . 1) (#\V . 5) (#\X . 10) (#\L . 50) (#\C . 100) (#\D . 500) (#\M . 1000)))

(define substracts
  #hasheq((#\M . #\C) (#\D . #\C) (#\C . #\X) (#\L . #\X) (#\X . #\I) (#\V . #\I)))

(define (to-roman n)
  (define digits (reverse (map car roman-digits)))
  (define values (make-immutable-hasheq roman-digits))
  (define (value digit) (hash-ref values digit))
  (define (substract digit) (hash-ref substracts digit #f))
  (define (iter n ds acc)
    (let* ([d (first ds)]
           [v (value d)]
           [s (substract d)])
      (cond [(zero? n) acc]
            [(>= n v) (iter (- n v) ds (cons d acc))]
            [(and s (>= n (- v (value s))))
             (iter (+ n (- v) (value s))
                   (rest ds)
                   (list* d s acc))]
            [else (iter n (rest ds) acc)])))
  (list->string (reverse (iter n digits '()))))
