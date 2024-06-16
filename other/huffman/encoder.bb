#!/usr/bin/env bb
(ns encoder
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

;; tree = nil | [tree tree]
;; TODO search for idiomatic way to store tuples
(defn make-tree [nodes]
  (loop [nodes nodes
         stack '()]
    (cond (empty? nodes) (first stack)

          (= "C" (first nodes))
          (recur (rest nodes)
                 (conj (drop 2 stack) [(second stack) (first stack)]))

          (= \P (first (first nodes)))
          (recur (rest nodes)
                 (conj stack (second (first nodes))))

          :else (throw (ex-info "unexpected node" (first nodes))))))

(comment
  (def t-nodes ["Pa" "Pb" "Pc" "C" "C"])
  (type (map identity t-nodes))
  (def lseq (lazy-seq (cons 1 (lazy-seq (cons 2 nil)))))
  (realized? lseq)
  (= "C" (last t-nodes))
  ababcaca  )

(defn encode-tree [tree]
  (cond (nil? tree) nil
        (char? tree) [[tree nil]]
        :else (mapcat (fn [code encoded]
                        (map (fn [[ch s]] [ch (cons code s)]) encoded))
                      [\0 \1]
                      (map encode-tree tree))))

(defn encode-char [tree ch]
  (->> tree
       (filter #(= ch (first %)))
       first second (apply str)))

(defn encode [tree s]
  (str/join (map (partial encode-char tree) s)))

(defn -main []
  (let [n (Integer/parseInt (read-line))
        nodes (doall (for [i (range n)] (read-line)))
        s (read-line)]
    (println (encode (encode-tree (make-tree nodes)) s))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
