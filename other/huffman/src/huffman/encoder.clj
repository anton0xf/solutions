(ns huffman.encoder
  (:require [clojure.string :as str]))

;; character to binary string
(defn encode-char [tree ch]
  (->> tree
       (filter #(= ch (first %)))
       first second (apply str)))

(defn encode [tree s]
  (str/join (map (partial encode-char tree) s)))
