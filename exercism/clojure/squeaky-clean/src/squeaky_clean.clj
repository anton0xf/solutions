(ns squeaky-clean
  (:require [clojure.string :as str]))

(defn capitalize
  "Capitalize first letter of the word"
  [w]
  (case (.length w)
    0 w
    1 (str/upper-case w)
    (str (str/upper-case (.substring w 0 1))
         (.substring w 1))))

(defn convert-case
  "Convert kebab-case to camelCase"
  [s]
  (let [[word & words] (str/split s #"-+")]
    (str/join (cons word (map capitalize words)))))

(defn clean
  "Replace spaces with underscores and control characters with placeholder.
  Convert kebab-case to camelCase.
  "
  [s]
  (-> s
      (str/replace " " "_")
      (str/replace #"[\u0000-\u001F\u007F-\u009F]" "CTRL")
      convert-case
      (str/replace #"[^_\p{IsAlphabetic}]+" "")
      (str/replace #"[α-ω]+" "")))
