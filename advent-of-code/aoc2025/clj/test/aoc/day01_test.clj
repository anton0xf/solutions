(ns aoc.day01-test
  (:require [aoc.day01 :refer :all]
            [clojure.test :refer :all]
            [clojure.java.io :as io]))

(defn multiples-in-range-ref
  "how many numbers n exist, such that a <= n*k <= b"
  [a b k]
  (if (< b a) (recur b a k)
      (->> (range a (inc b))
           (filter #(zero? (rem % k)))
           count)))

(deftest test-multiples-in-range
  (testing "test ref"
    (is (= 5 (multiples-in-range-ref -1 3 1)))
    (is (= 3 (multiples-in-range-ref 1 3 1)))
    (is (= 4 (multiples-in-range-ref -3 5 2)))
    (is (= 5 (multiples-in-range-ref -4 5 2)))
    (is (= 5 (multiples-in-range-ref -3 6 2)))
    (is (= 0 (multiples-in-range-ref 1 4 5))))
  (testing "test actual impl"
    (for [k (range 1 8)
          a (range -10 11)
          b (range -10 11)]
      (do (println "[k a b] =" [k a b])
          (is (= (multiples-in-range-ref a b k) (multiples-in-range a b k)))))))

(deftest test-exec
  (testing "Should work on example"
    (let [s (slurp (io/resource "day01/example.txt"))
          cmds (parse s)]
      (is (= [50 82 52 0 95 55 0 99 0 14 32]
             (map first (exec 50 cmds))))
      (is (= [0 1 0 1 0 1 1 0 1 0 1]
             (map second (exec 50 cmds)))))))



