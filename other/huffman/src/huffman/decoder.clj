(ns huffman.decoder
  (:require [clojure.string :as str]
            [clojure.core.match :refer [match]]))

;; read one character from sequence of 0/1 characters (or binary string)
;; return a pair of a character and rest of input sequence
(defn decode-char [tree chars]
  (match [tree (seq chars)]
    [[_ _] ([] :seq)] (throw (RuntimeException. "unexpected end of input string"))
    [[left right] ([ch & r] :seq)] (recur (case ch, \0 left, \1 right,
                                                (throw (RuntimeException. (str "unexpected binary char " \a))))
                                          r) 
    [ch r] [ch r]))

(defn decode [tree s]
  (str/join
   (loop [s s
          res []]
     (if (empty? s) res
         (let [[char new-s] (decode-char tree s)]
           (recur new-s (conj res char)))))))
