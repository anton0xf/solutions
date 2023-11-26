#lang racket

(provide make-robot
         name
         reset!
         reset-name-cache!)

;; Return a random char between [FROM, TO]
(define (random-char from to)
  (integer->char
   (+ (char->integer from)
      (random
       (add1 (- (char->integer to)
                (char->integer from)))))))

(module+ test
  (require rackunit)
  (check-true (char<=? #\A (random-char #\A #\Z) #\Z))
  (check-true (char<=? #\0 (random-char #\0 #\9) #\9))
  (check-true (char=? #\0 (random-char #\0 #\0))))

(define cache (make-hash))

(define (make-robot)
  (let ([robot (string (random-char #\A #\Z)
                       (random-char #\A #\Z)
                       (random-char #\0 #\9)
                       (random-char #\0 #\9)
                       (random-char #\0 #\9))])
    (if (hash-ref cache robot #f)
        (make-robot)
        (begin0 robot
          (hash-set! cache robot #t)))))

(define (name robot) robot)
(define (reset! robot) (make-robot))
(define (reset-name-cache!) (hash-clear! cache))
