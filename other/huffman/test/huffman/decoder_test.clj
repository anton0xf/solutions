(ns huffman.decoder-test
  (:require [huffman.decoder :refer :all]
            [clojure.test :refer :all]))

(def tree [[\a \b] \c])

(deftest decode-char-test
  (is (= [\c nil] (decode-char tree "1")))
  (is (= [\c (seq "00")] (decode-char tree "100")))
  (is (= [\a nil] (decode-char tree "00")))
  (is (= [\b nil] (decode-char tree "01"))))

(deftest decode-test
  (is (= "cab" (decode tree "10001"))))
