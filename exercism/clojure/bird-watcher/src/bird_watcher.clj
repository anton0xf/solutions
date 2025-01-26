(ns bird-watcher)

(def last-week 
  [0 2 5 3 7 8 4])

(defn today [birds]
  (peek birds))

(defn inc-bird [birds]
  (conj (pop birds) (inc (today birds))))

(defn day-without-birds? [birds]
  (true? (some zero? birds)))

(defn n-days-count [birds n]
  (reduce + 0 (take n birds)))

(defn busy-days [birds]
  (count (filter #(>= % 5) birds)))

(defn odd-week? [birds]
  (loop [x (first birds)
         xs (rest birds)]
    (cond
      (not (contains? #{0 1} x)) false
      (empty? xs) true
      (not= x (first xs)) (recur (first xs) (rest xs)))))
