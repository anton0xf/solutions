;; <5 kyu> Perimeter of squares in a rectangle
;; https://www.codewars.com/kata/559a28007caad2ac4e000083
(ns perimeter.core)

(defn fib [n] 
  (loop [a 1 b 1 m 0]
    (if (= m n) a
        (recur b (+ a b) (inc m)))))

;; (take 10 (map fib (range)))
;; => (1 1 2 3 5 8 13 21 34 55)

(defn perimeter [n]
  (* 4 (dec (fib (+ n 2)))))

;; (perimeter 5) ;; => 80
;; (perimeter 7) ;; => 216
