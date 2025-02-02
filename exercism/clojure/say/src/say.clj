(ns say
  (:require [clojure.string :as str]))

(def digits
  {0 "zero", 1 "one", 2 "two", 3 "three", 4 "four", 5 "five",
   6 "six", 7 "seven", 8 "eight", 9 "nine"})

(def ten+
  {10 "ten", 11 "eleven", 12 "twelve", 13 "thirteen", 14 "fourteen", 15 "fifteen",
   16 "sixteen", 17 "seventeen", 18 "eighteen", 19 "nineteen"})

(def tens
  {2 "twenty", 3 "thirty", 4 "forty", 5 "fifty",
   6 "sixty", 7 "seventy", 8 "eighty", 9 "ninety"})

(defn two-digit [n]
  (assert (<= 0 n 99))
  (cond
    (< n 10) (digits n)
    (< n 20) (ten+ n)
    :else (let [a (quot n 10), b (rem n 10)]
            (if (zero? b) (tens a)
                (str (tens a) "-" (digits b))))))

(defn three-digit [n]
  (assert (<= 0 n 999))
  (let [a (quot n 100), bc (rem n 100)]
    (cond (zero? a) (two-digit bc)
          (zero? bc) (str (digits a) " hundred")
          :else (str (digits a) " hundred " (two-digit bc)))))

(defn split-groups
  "split into groups by 10^3 big-endian"
  [n]
  (loop [n n, acc []]
    (if (zero? n) acc
        (recur (quot n 1000)
               (conj acc (rem n 1000))))))

(def group-names [nil "thousand" "million" "billion"])

(defn number [n]
  (when-not (<= 0N n (bigint (apply str (repeat 4 "999"))))
    (throw (IllegalArgumentException. "out of range")))
  (if (zero? n) (digits n)
      (->> (map (fn [group name] (when-not (zero? group)
                                   [(three-digit group) name]))
                (split-groups n)
                group-names)
           reverse
           (apply concat)
           (filter some?)
           (str/join " "))))
