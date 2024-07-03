(ns huffman.tree-test
  (:require  [clojure.test :refer :all]
             [huffman.tree :refer :all]))

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
