(ns encoder-test
  (:require [encoder :refer :all]
            [clojure.test :refer :all]))

(deftest make-tree-test
  (is (nil? (make-tree [])))
  (is (= [\a \b] (make-tree ["Pa" "Pb" "C"])))
  (is (= [[\a \b] \c] (make-tree ["Pa" "Pb" "C" "Pc" "C"])))
  (is (= [\a [\b \c]] (make-tree ["Pa" "Pb" "Pc" "C" "C"])))
  (is (= [[\a \b] [\c \d]] (make-tree ["Pa" "Pb" "C" "Pc" "Pd" "C" "C"]))))

(deftest encode-tree-test
  (is (= [[\a nil]] (encode-tree \a)))
  (is (= '([\a (\0)] [\b (\1)]) (encode-tree [\a \b])))
  (is (= '([\a (\0)] [\b (\1 \0)] [\c (\1 \1)])
         (encode-tree [\a [\b \c]]))))

(deftest encode-char-test
  (is (= "0" (encode-char (encode-tree [\a [\b \c]]) \a)))
  (is (= "10" (encode-char (encode-tree [\a [\b \c]]) \b)))
  (is (= "11" (encode-char (encode-tree [\a [\b \c]]) \c))))

(deftest encode-test
  (is (= "010010110110" (encode [\a [\b \c]] "ababcaca"))))
