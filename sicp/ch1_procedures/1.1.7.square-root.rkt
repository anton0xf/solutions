#lang sicp

(define (square x) (* x x))
(define (average x y) (/ (+ x y) 2))

(define (sqrt a)
  (define (iter x)
    (if (good-enough? x) x
        (iter (improve x))))
  (define (good-enough? x)
    (> 0.001 (abs (- (square x) a))))
  (define (improve x)
    (average x (/ a x)))
  (iter 1.0))

;; (sqrt 25.) ;; => 5

;; Exercise 1.7: better good-enough?
(define (sqrt2 a)
  (define (iter x0 x1)
    (if (good-enough? x0 x1) x1
        (iter x1 (improve x1))))
  (define (good-enough? x0 x1)
    (> 0.001 (abs (/ (- x0 x1) x0))))
  (define (improve x)
    (average x (/ a x)))
  (iter 1.0 (improve 1.0)))

;; (sqrt  0.0001) ;; => 0.03230844833048122
;; (sqrt2 0.0001) ;; => 0.010000000025490743

;; (sqrt (* 10 (square (square (square (square (square 10000)))))))
;; hangs

;; (sqrt2 (* 100 (square (square (square (square (square 10000)))))))
;; 1.0000000962016394e+65

;; Exercise 1.8: cube root
(define (close? x0 x1)
  (> 0.001 (abs (/ (- x0 x1) (max x0 x1)))))

(define (cube-root a)
  (define (iter x0 x1)
    (if (close? x0 x1) x1
        (iter x1 (improve x1))))
  (define (improve x)
    (* 1/3 (+ (* 2 x) (/ a x x))))
  (iter 1.0 (improve 1.0)))

(define (cube x) (* x x x))

;; (cube-root (cube 123))
;; (cube-root (cube 0.001))
;; (cube-root 0)
