(ns bob
  (:require [clojure.string :as str]))

(defn question? [s]
  (str/ends-with? (str/trimr s) "?"))

(defn yell?
  "s is in upper case and contains at least one letter"
  [s]
  (and (= s (str/upper-case s))
       (re-find #"[A-Z]" s)))

(defn silence? [s]
  (str/blank? s))

(defn response-for [s]
  (cond
    (and (question? s) (yell? s)) "Calm down, I know what I'm doing!"
    (question? s) "Sure."
    (yell? s) "Whoa, chill out!"
    (silence? s) "Fine. Be that way!"
    :else "Whatever."))
