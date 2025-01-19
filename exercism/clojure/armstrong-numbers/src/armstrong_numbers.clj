(ns armstrong-numbers
  (:require [clojure.math :refer [pow]]))

(defn digits [n]
  (loop [n n, acc nil]
    (if (zero? n) (or acc '(0))
        (recur (quot n 10) (conj acc (rem n 10))))))

(defn armstrong?
  "Returns true if the given number is an Armstrong number; otherwise, returns false"
  [num]
  (let [ds (digits num)
        p (count ds)]
    (== num
        (->> ds
             (map (fn [d] (.pow (biginteger d) p)))
             (reduce +)))))
