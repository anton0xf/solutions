;; <6 kyu> Multiples of 3 or 5
;; https://www.codewars.com/kata/514b92a657cdc65150000006
(ns multiples)

(defn s [n] (quot (* n (+ n 1)) 2))
;; (s 3) ;; => 6

(defn solution [n]
  (let [m (dec n)
        s3  (* 3  (s (quot m 3)))
        s5  (* 5  (s (quot m 5)))
        s15 (* 15 (s (quot m 15)))]
    (+ s3 s5 (- s15))))

;; (solution 10) ;; => 23
