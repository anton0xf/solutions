(ns log-levels
  (:require [clojure.string :as str]))

(defn parse-log [s]
  (let [[_ level message] (re-matches #"(?sm)^\[(\w+)\]:\s*(.*)$" s)]
    {:level (str/lower-case level)
     :message (str/trimr message)}))

(defn message
  "Takes a string representing a log line
   and returns its message with whitespace trimmed."
  [s]
  (:message (parse-log s)))

(defn log-level
  "Takes a string representing a log line
   and returns its level in lower-case."
  [s]
  (:level (parse-log s)))

(defn reformat
  "Takes a string representing a log line and formats it
   with the message first and the log level in parentheses."
  [s]
  (let [{:keys [level message]} (parse-log s)]
    (format "%s (%s)" message level)))
