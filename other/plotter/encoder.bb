#!/usr/bin/env bb
(ns encoder
  (:require [clojure.java.io :as io]))

(defn size [lines]
  [(count lines)
   (count (first lines))])
(comment
  (size ["asdf" "qwer"]) ;; => [2 4]
  )

(defn next-pos [[nrows ncols] [row col]]
  (if (>= col ncols)
    (if (>= row nrows) nil [(inc row) 0])
    [row (inc col)]))

(defn next-char [sz pos lines]
  (if (>= col ncols)
    (if (>= row nrows) nil [(inc row) 0])
    [row (inc col)]))

(defn encode [lines]
  (let [sz (size lines)] ;; rows * cols
    (loop [pos [0 0]
           lines lines
           code []] ;; vector of instructions
      (let [[[ch p] ls] (next-printable-char sz pos lines)]
        (if ch
          (recur (next-pos sz p) ls
                 (conj code (move pos p)))
          (code-to-str code))))))

(defn main []
  (let [lines (line-seq (io/reader *in*))]
    (prinlnt (encode lines))))
