#lang racket

(provide make-robot
         name
         reset!
         reset-name-cache!)

(define name-cache (mutable-set))

(define (reset-name-cache!)
  (set! name-cache (mutable-set)))
(define (add-to-name-cache! name)
  (set-add! name-cache name))
(define (is-name-used? name)
  (set-member? name-cache name))

(define (random-char from to)
  (integer->char
   (random (char->integer from)
           (add1 (char->integer to)))))

(define (random-letter)
  (random-char #\A #\Z))

(define (random-number)
  (random-char #\0 #\9))

(define (random-name)
  (string (random-letter) (random-letter)
          (random-number) (random-number) (random-number)))

(define (gen-name)
  (let ([name (random-name)])
    (if (is-name-used? name)
        (gen-name)
        (begin (add-to-name-cache! name)
               name))))

(define (make-robot)
  (box (gen-name)))
(define (name robot)
  (unbox robot))
(define (reset! robot)
  (set-box! robot (gen-name)))
