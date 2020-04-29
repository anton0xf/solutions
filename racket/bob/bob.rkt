#lang racket
(provide response-for)

(define (string-empty? s)
  (string=? "" s))

(define (yell? s)
  (and
   ;; there is at least one letter
   (findf char-alphabetic? (string->list s))
   ;; all letters are in upper case
   (string=? s (string-upcase s))))

(define (question? s)
  (string-suffix? s "?"))

(define (yell-question? s)
  (and (yell? s) (question? s)))

(define (any-string? s) #t)

;;; list of pairs: (condition-function . answer-string)
(define rules
  `((,string-empty? . "Fine. Be that way!")
    (,yell-question? . "Calm down, I know what I'm doing!")
    (,question? . "Sure.")
    (,yell? . "Whoa, chill out!")
    (,any-string? . "Whatever.")))

(define (response-for phrase)
  (define (check condition)
    (condition (string-trim phrase)))
  (cdr (assf check rules)))
