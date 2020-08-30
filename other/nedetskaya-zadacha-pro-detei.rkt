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

;; lists all different n-tuples (sorted in descending order)
;; of positive integers with a given sum
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

;; все варианты возрастов с заданной суммой - 13 лет
(define ages (sums-n 3 13))

(define (non-uniq-prod xss)
  (define (prod xs) (apply * xs))
  (define (not-single xs) (< 1 (length xs)))
  (~>> xss
       (group-by prod)
       (filter not-single)
       (apply append)))

;; check that max of descending sorted xs is uniq
(define (uniq-max? xs)
  (> (first xs) (second xs)))

(define answer
  (filter uniq-max? (non-uniq-prod ages)))
