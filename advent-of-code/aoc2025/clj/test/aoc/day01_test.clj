(ns aoc.day01-test
  (:require [aoc.day01 :refer :all]
            [clojure.test :refer :all]
            [clojure.java.io :as io]))

(deftest test-exec
  (testing "Should work on example"
    (let [s (slurp (io/resource "day01/example.txt"))
          cmds (parse s)]
      (is (= [50 82 52 0 95 55 0 99 0 14 32]
             (exec 50 cmds))))))



