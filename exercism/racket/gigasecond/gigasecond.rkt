#lang racket
(provide add-gigasecond)
(require racket/date
         threading)

(define gigasecond (expt 10 9))

(define (add-gigasecond dt)
  (~> (date->seconds dt)
      (+ gigasecond)
      (seconds->date)))
