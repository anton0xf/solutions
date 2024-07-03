(ns huffman.encoder-test
  (:require [huffman.encoder :refer :all]
            [huffman.tree :refer :all]
            [clojure.test :refer :all]))

(deftest encode-char-test
  (is (= "0" (encode-char (encode-tree [\a [\b \c]]) \a)))
  (is (= "10" (encode-char (encode-tree [\a [\b \c]]) \b)))
  (is (= "11" (encode-char (encode-tree [\a [\b \c]]) \c))))

(deftest encode-test
  (is (= "010010110110" (encode (encode-tree [\a [\b \c]]) "ababcaca"))))
