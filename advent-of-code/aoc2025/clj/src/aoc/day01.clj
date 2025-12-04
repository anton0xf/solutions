(ns aoc.day01
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

(defn parse [s]
  (->> (str/split-lines s)
       (map (fn [s] [(.substring s 0 1)
                     (Integer/parseInt (.substring s 1))]))))

(defn step [n cmd k]
  (let [m (if (= "R" cmd) k (- k))]
    (mod (+ n m) 100)))

(defn exec [init cmds]
  (loop [n init, cmds cmds, res [init]]
    (if (empty? cmds) res
        (let [[[cmd k] & rest] cmds
              next (step n cmd k)]
          (recur next rest (conj res next))))))

(defn part1 [cmds]
  (->> (exec 50 cmds)
       (filter #(= 0 %)) count))

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
  true))
