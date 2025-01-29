(ns raindrops
  (:require [clojure.string :as str]))

(defn div?
  "is n divisible by div?"
  [n div]
  (zero? (rem n div)))

(defn convert [n]
  (let [s (str/join [(if (div? n 3) "Pling" "")
                     (if (div? n 5) "Plang" "")
                     (if (div? n 7) "Plong" "")])]
    (if (= s "") (str n) s)))

