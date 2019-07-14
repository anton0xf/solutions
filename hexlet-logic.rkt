#lang racket
(module+ test
  (require rackunit))

(define bool '(0 1))

(define (is-false? b) (eq? b 0))
(define (is-true? b) (eq? b 1))

(define (set-pow s p)
  (apply cartesian-product
         (make-list p s)))

(define (list-bool-funcs n)
  (define args (set-pow bool n))
  (define all-vals (set-pow bool (length args)))
  (define (build-func vals) (map list args vals))
  (map build-func all-vals))

(module+ test
  (test-case "(list-bool-funcs n)"
    (check-equal?
     (list-bool-funcs 1)
     '((((0) 0) ((1) 0))
       (((0) 0) ((1) 1))
       (((0) 1) ((1) 0))
       (((0) 1) ((1) 1))))
    (check-equal?
     (list-bool-funcs 2)
     '((((0 0) 0) ((0 1) 0) ((1 0) 0) ((1 1) 0))
       (((0 0) 0) ((0 1) 0) ((1 0) 0) ((1 1) 1))
       (((0 0) 0) ((0 1) 0) ((1 0) 1) ((1 1) 0))
       (((0 0) 0) ((0 1) 0) ((1 0) 1) ((1 1) 1))
       (((0 0) 0) ((0 1) 1) ((1 0) 0) ((1 1) 0))
       (((0 0) 0) ((0 1) 1) ((1 0) 0) ((1 1) 1))
       (((0 0) 0) ((0 1) 1) ((1 0) 1) ((1 1) 0))
       (((0 0) 0) ((0 1) 1) ((1 0) 1) ((1 1) 1))
       (((0 0) 1) ((0 1) 0) ((1 0) 0) ((1 1) 0))
       (((0 0) 1) ((0 1) 0) ((1 0) 0) ((1 1) 1))
       (((0 0) 1) ((0 1) 0) ((1 0) 1) ((1 1) 0))
       (((0 0) 1) ((0 1) 0) ((1 0) 1) ((1 1) 1))
       (((0 0) 1) ((0 1) 1) ((1 0) 0) ((1 1) 0))
       (((0 0) 1) ((0 1) 1) ((1 0) 0) ((1 1) 1))
       (((0 0) 1) ((0 1) 1) ((1 0) 1) ((1 1) 0))
       (((0 0) 1) ((0 1) 1) ((1 0) 1) ((1 1) 1))))))

(define conjunction
  '(((0 0) 0)
    ((0 1) 0)
    ((1 0) 0)
    ((1 1) 1)))

(define disjunction
  '(((0 0) 0)
    ((0 1) 1)
    ((1 0) 1)
    ((1 1) 1)))

(define implication
  '(((0 0) 1)
    ((0 1) 1)
    ((1 0) 0)
    ((1 1) 1)))

(define biconditional
  '(((0 0) 1)
    ((0 1) 0)
    ((1 0) 0)
    ((1 1) 1)))

(define (eval-bool-func f args)
  (second (assoc args f)))

(module+ test
  (test-case "(eval-bool-func f args)"
    (check-eq? (eval-bool-func implication '(0 0)) 1)
    (check-eq? (eval-bool-func implication '(0 1)) 1)
    (check-eq? (eval-bool-func implication '(1 0)) 0)
    (check-eq? (eval-bool-func implication '(1 1)) 1)))

(define (list-refs lst poss)
  (for/list ([pos poss])
    (list-ref lst pos)))

;; list all boolean bi-functions
;; satisfying implication transitive property

;; → is transitive, when for all booleans a, b and c
;; (a → b) & (b → c) → (a → c)

(define (is-transitive? f)
  (define args (set-pow bool 3))
  (define (get-args poss)
    (for/list ([lst args]) 
      (list-refs lst poss)))
  (define ab (get-args '(0 1)))
  (define bc (get-args '(1 2)))
  (define ac (get-args '(0 2)))
  (define (apply-f f argss)
    (for/list ([args argss])
      (eval-bool-func f args)))
  (define f-ab (apply-f f ab))
  (define f-bc (apply-f f bc))
  (define f-ac (apply-f f ac))
  (define conj (apply-f conjunction
                        (map list f-ab f-bc)))
  (define res (apply-f f ;; implication
                       (map list conj f-ac)))
    (andmap is-true? res))

(module+ test
  (test-case "(is-transitive? f)"
    (check-true (is-transitive? implication))
    (check-false (is-transitive? disjunction))))

(define (filter-bi-funcs pred?)
  (filter pred? (list-bool-funcs 2)))

;; list all boolean bi-functions satisfying property:
;; (a <-> b) -> (a -> b)
(define (is-implied-by-bincondition? f)
  (define args (set-pow bool 2))
  (define (apply-f f argss)
    (for/list ([args argss])
      (eval-bool-func f args)))
  (define bicond (apply-f biconditional args))
  (define impl (apply-f implication args))
  (define res
    (apply-f f (map list bicond impl)))
  (andmap is-true? res))


