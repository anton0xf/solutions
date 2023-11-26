#lang racket
(provide response-for)
(require syntax/parse/define)

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

;; ничего тут не понимаю см. TODO про это
(define-simple-macro
  (switch value:expr (rule:id result:expr) ...)
  (cond [(rule value) result] ...))

(define (response-for phrase)
  (switch (string-trim phrase)
          [string-empty? "Fine. Be that way!"]
          [yell-question? "Calm down, I know what I'm doing!"]
          [question? "Sure."]
          [yell? "Whoa, chill out!"]
          [any-string? "Whatever."]))
