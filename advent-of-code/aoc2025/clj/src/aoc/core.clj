(ns aoc.core (:gen-class))

(defn -main [& args]
  (when (empty? args)
    (binding [*out* *err*]
      (println "Usage: aoc day-name [input-path]")
      (println "Examples:")
      (println "\taoc day01")
      (println "\taoc day01 day01/example.txt"))
    (System/exit 1))
  (let [day (first args)
        path (or (second args) (str day "/input.txt"))]
    ((requiring-resolve (symbol (str "aoc." day "/run"))) path)))

