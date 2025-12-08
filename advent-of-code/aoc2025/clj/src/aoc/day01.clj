(ns aoc.day01
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.math :refer [floor-div]]))

(defn parse [s]
  (->> (str/split-lines s)
       (map (fn [s] [(.substring s 0 1)
                     (Integer/parseInt (.substring s 1))]))))

(defn ceil-div ^long [^long x ^long y]
  (java.lang.Math/ceilDiv x y))

(defn range-len [a b]
  (if (> a b) 0
      (- (inc b) a)))

(defn multiples-in-range
  "how many numbers n exist, such that a <= n*k <= b, if a <= b, or vice versa"
  [a b k]
  ;; ceil(a/k) <= n <= floor(b/k)
  (range-len (ceil-div (min a b) k)
             (floor-div (max a b) k)))

(defn step [n cmd k]
  (let [m (if (= "R" cmd) k (- k))
        d 100
        next (+ n m)]
    [(mod next d) ;; next position
     ;; how many multiplies of 100 where met, excluding n
     (- (multiples-in-range n next d)
        (if (zero? (mod n d)) 1 0))
     ]))

(defn exec [init cmds]
  (loop [n init, cmds cmds, res [[init 0]]]
    (if (empty? cmds) res
        (let [[[cmd k] & rest] cmds
              [next m :as r] (step n cmd k)]
          (recur next rest (conj res r))))))

(defn part1 [cmds]
  (->> (exec 50 cmds)
       (filter #(= 0 (first %))) count))

(defn part2 [cmds]
  (->> (exec 50 cmds)
       (map second)
       (reduce + 0)))

(comment
  (def ex (slurp (io/resource "day01/example.txt")))
  (->> (parse ex) (exec 50))
  ;; => [50 82 52 0 95 55 0 99 0 14 32]
  (->> (parse ex) (exec 50)
       (filter #(= 0 %)) count)

  (->> (io/resource "day01/input.txt")
       slurp parse (exec 50)
       (filter #(= 0 %)) count)
  )

(defn run [path]
  (let [cmds (parse (slurp (io/resource path)))]
    (println "part1:" (part1 cmds))
    (println "part2:" (part2 cmds))
    true))
