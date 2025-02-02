(ns wordy
  (:require [clojure.string :as str]))

(defn int-str? [s]
  (re-matches #"-?\d+" s))

(defn error [msg]
  (throw (IllegalArgumentException. msg)))

(defn syntax-error []
  (error "syntax error"))

(defn unknown-op []
  (error "unknown operation"))

(defn parse-int [args]
  (if (and (seq args) (int-str? (first args)))
    [(Integer/parseInt (first args)) (rest args)]
    (syntax-error)))

(defn skip [s args]
  (if (and (seq args) (= s (first args)))
    (rest args)
    (syntax-error)))

(defn parse-op [args]
  (when (seq args)
    (case (first args)
      "plus" [+ (rest args)]
      "minus" [- (rest args)]
      "multiplied" [* (skip "by" (rest args))]
      "divided" [/ (skip "by" (rest args))]
      (if (int-str? (first args))
        (syntax-error)
        (unknown-op)))))

(defn calculate [args]
  (loop [[n args] (parse-int args)]
    (if (empty? args) n
        (let [[op args] (parse-op args)
              [m args] (parse-int args)]
          (recur [(op n m) args])))))

(defn evaluate
  "Evaluates a simple math problem"
  [question]
  (if-let [[_ q] (re-matches #"^What is (.*)\?$" question)]
    (calculate (str/split (str/trim q) #"\s+"))
    (syntax-error)))
