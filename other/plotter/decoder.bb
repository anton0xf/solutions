#!/usr/bin/env bb
(ns decoder
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

(defn parse-int [s] (Integer/parseInt s))
(defn parse-moves [s]
  (if (empty? s) 1
      (parse-int s)))

(defn parse-code [code]
  (for [[_ move moves print ch] (re-seq #"([DURL])(\d*)|(P)(.)" code)]
    (if move
      [:move move (parse-moves moves)]
      [:print print (first ch)])))

(comment 
  (def code "DR3P*RP*RP*DP*DP*LP*LP*UP*")
  (re-seq #"([DURL])(\d*)|(P)(.)" code)
  ;; => (["D" "D" "" nil nil]
  ;;     ["R3" "R" "3" nil nil]
  ;;     ["P*" nil nil "P" "*"]
  ;;     ...)
  (parse-code code)
  ;; => ([:move "D" 1] [:move "R" 3] [:print "P" \*] ...)
  )

(defn move [[row col] comm n]
  (case comm
    "D" [(+ row n) col]
    "U" [(- row n) col]
    "R" [row (+ col n)]
    "L" [row (- col n)]))

(defn exec-on-map [commands]
  (loop [pos [0 0] ;; point is pair of [row col], idexed from zero
         cs commands
         m {}]
    (if-let [[[comm-type comm arg] & cs] cs]
      (case comm-type
        :move (recur (move pos comm arg) cs m)
        :print (recur pos cs (conj m [pos arg])))
      m)))
(comment
  (exec-on-map (parse-code code))
  ;; => {[1 3] \*, [1 4] \*, [1 5] \*, [2 5] \*, [3 5] \*, [3 4] \*, [3 3] \*, [2 3] \*}
  )

(defn exec [[rows cols] commands]
  (let [chars-map (exec-on-map commands)]
    (str/join \newline
              (for [row (range rows)]
                (str/join (for [col (range cols)]
                            (get chars-map [row col] \space)))))))
(comment
  (exec [4 6] (parse-code code))
  ;; => "      \n   ***\n   * *\n   ***"
  )

(defn main []
  (let [[rows-str cols-str code] (line-seq (io/reader *in*))
        rows (parse-int rows-str)
        cols (parse-int cols-str)
        commands (parse-code code)]
    (println (exec [rows cols] commands))))

(main)
