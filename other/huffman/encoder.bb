#!/usr/bin/env bb
(ns encoder
  (:require [huffman.tree :refer :all]
            [huffman.encoder :refer [encode]]
            [clojure.java.io :as io]))

(defn -main []
  (let [n (Integer/parseInt (read-line))
        nodes (doall (for [i (range n)] (read-line)))
        s (read-line)]
    (println (encode (encode-tree (make-tree nodes)) s))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
