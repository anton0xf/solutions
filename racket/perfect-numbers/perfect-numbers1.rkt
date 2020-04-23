#lang racket
(provide classify)

;; Given positive integer it returns list of pairs: prime factor and it's power.
;; See https://en.wikipedia.org/wiki/Trial_division
(define (prime-factors n)
  (if (= 1 n) '()
      (for/fold ([n n]
                 [res '()]
                 #:result (if (= 1 n) res
                              (cons (list n 1) res)))
                ([d (stream-cons ; 2 3 5 7 ... sqrt(n)
                     2 (in-range 3 (add1 (ceiling (sqrt n))) 2))]
                 #:break (= 1 n)
                 #:when (zero? (remainder n d)))
        (let iter ([n n] [pow 0])
          (if (zero? (remainder n d))
              (iter (/ n d) (add1 pow))
              (values n (cons (list d pow) res)))))))

(define (aliquot-sum0 n)
  (for/sum ([d (range 1 n)]
            #:when (zero? (remainder n d)))
    d))

;; See https://en.wikipedia.org/wiki/Divisor_function
;; or https://math.stackexchange.com/a/163246/406814
(define (aliquot-sum n)
  (define factors (prime-factors n))
  (let ([sum (for/product ([d (map first factors)] ; divisor
                           [p (map second factors)]) ; power
               ;; 1 + d + d^2 + ... + d^p = (d^(p+1) - 1) / (d - 1)
               (/ (sub1 (expt d (add1 p)))
                  (sub1 d)))])
    (- sum n)))

(define (classify n)
  (define sum (aliquot-sum n))
  (cond [(= n sum) 'perfect]
        [(< n sum) 'abundant]
        [else 'deficient]))
