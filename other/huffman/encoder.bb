#!/usr/bin/env bb
(ns encoder
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))
(defn make-tree [stack] )
(comment
  ("Pa" "Pb" "Pc" "C" "C")
  ababcaca  )

(defn main []
  (let [n (Integer/parseInt (read-line))
        stack (doall (for [i (range n)] (read-line)))
        s (read-line)]
    (println n stack s)
    ;; (println (encode lines))
    ))

(main)
