#lang racket
;; https://vk.com/@thecode.media-nedetskaya-zadacha-pro-detei

;; Встречаются два программиста, которые давно друг друга не видели.
;; У них происходит такой диалог:
;; — Я слышал, у тебя дети появились.
;; — Да, три сына.
;; — И сколько им лет?
;; — Ну... В сумме — тринадцать!
;; — Хм... Ты снова загадками говоришь? Ну ладно. Что ещё можешь сказать?
;; — Если возрасты перемножить, получится столько же, сколько окон вон у того дома.
;; Программист считает окна и прикидывает варианты.
;; — Но этого до сих пор недостаточно для ответа!
;; — Могу добавить, что мой старший сын — рыжий.
;; — Ну теперь совсем другое дело. Им ... (далее следует ответ).
;; — Правильно!
;; Сколько же лет им было? И как первый смог вычислить возраст?

(require threading)

(module+ test (require rackunit))

(define (set-equal? xs ys)
  (equal? (list->set xs)
          (list->set ys)))

(module+ test
  (test-case "(set-equal? list1 list2)"
    (check-true (set-equal? '(1 2 3) '(3 2 1)))
    (check-false (set-equal? '(1 2 3) '(2 1)))
    (check-false (set-equal? '(1 2) '(3 2 1)))))

(module+ test
  (define-binary-check
    (check-set-equal? set-equal? actual expected)))

;; list all different pairs of positive natural numbers
;; with passed sum
(define (sums-2 sum)
  (filter
   (λ (x) (>= (first x) (second x) 1))
   (map (λ (n1) (list n1 (- sum n1)))
        (map add1 (range sum)))))

(module+ test
  (test-case "(sums-2 sum)"
    (check-set-equal? (sums-2 1) '())
    (check-set-equal? (sums-2 2) '((1 1)))
    (check-set-equal? (sums-2 3) '((2 1)))
    (check-set-equal? (sums-2 4) '((3 1) (2 2)))
    (check-set-equal? (sums-2 5) '((4 1) (3 2)))
    (check-set-equal? (sums-2 6) '((5 1) (4 2) (3 3)))))

;; (define (sum-inc-n ms)
;;   (map (λ (m) (cons (list m)
;;                     (sums-2 m)))
;;        ms))

;; (define (sums-n n sum)
;;   (cond
;;     [(> n sum) empty]
;;     [(> n 2)
;;      (map
;;       sum-inc-n
;;       (sums-n (sub1 n) sum))]
;;     [(= n 2) (sums-2 sum)]
;;     [(= n 1) (list sum)]
;;     [else empty]))

(define (sums-n n sum)
  (~>> (make-list n sum)
       (map (λ (m) (range 1 (add1 m))))
       (apply cartesian-product)
       (map (λ (lst) (sort lst >)))
       remove-duplicates
       (filter (λ (lst) (= sum (apply + lst))))))

(module+ test
  (test-case "(sums-n n sum)"
    (check-set-equal? (sums-n 2 1) '())
    (check-set-equal? (sums-n 2 2) '((1 1)))
    (check-set-equal? (sums-n 2 3) '((2 1)))
    (check-set-equal? (sums-n 2 4) '((3 1) (2 2)))
    (check-set-equal? (sums-n 2 5) '((4 1) (3 2)))
    (check-set-equal? (sums-n 2 6) '((5 1) (4 2) (3 3)))

    (check-set-equal? (sums-n 3 1) '())
    (check-set-equal? (sums-n 3 2) '())
    (check-set-equal? (sums-n 3 3) '((1 1 1)))
    (check-set-equal? (sums-n 3 4) '((2 1 1)))
    (check-set-equal? (sums-n 3 5) '((3 1 1) (2 2 1)))
    (check-set-equal? (sums-n 3 6) '((4 1 1) (3 2 1) (2 2 2)))))
