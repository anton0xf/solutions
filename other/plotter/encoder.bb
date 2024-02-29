#!/usr/bin/env bb
(ns encoder
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

;; point is pair of [row col], where rows and cols nums start from zero
(defn move [[r1 c1] [r2 c2]]
  (let [r (- r2 r1)
        c (- c2 c1)]
    (str (cond (zero? r) ""
               (= 1 r) "D"
               (pos? r) (str "D" r)
               (= -1 r) "U"
               :else (str "U" (- r)))
         (cond (zero? c) ""
               (= 1 c) "R"
               (pos? c) (str "R" c)
               (= -1 c) "L"
               :else (str "L" (- c))))))

(defn encode [lines]
  (let [indexed-chars (mapcat (fn [line row]
                                (map (fn [ch col] [ch [row col]])
                                     line (range)))
                              lines (range))]
    (loop [pos [0 0]
           chs (filter #(not= \space (first %)) indexed-chars)
           code []]
      (if-let [[[ch p] & chs] (seq chs)]
        (recur p chs (conj code (str (move pos p) "P" ch)))
        (str/join code)))))

(comment
  (encode [""
           "   ***"
           "   * *"
           "   ***"])
  ;; => "D1R3P*R1P*R1P*D1L2P*R2P*D1L2P*R1P*R1P*"
  )

(defn main []
  (let [lines (line-seq (io/reader *in*))]
    (println (count lines))
    (println (reduce max (map count lines)))
    (println (encode lines))))

(main)
