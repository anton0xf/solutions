(ns triangle)

(defn triangle? [a b c]
  (and (pos? a) (pos? b) (pos? c)
       (<= a (+ b c))
       (<= b (+ a c))
       (<= c (+ a b))))

(defn equilateral?
  "Returns true if the triangle with sides a, b, and c is equilateral; otherwise, returns false"
  [a b c]
  (and (pos? a) (= a b c)))

(defn isosceles?
  "Returns true if the triangle with sides a, b, and c is isosceles; otherwise, returns false"
  [a b c]
  (and (triangle? a b c)
       (or (= a b)
           (= a c)
           (= b c))))

(defn scalene?
  "Returns true if the triangle with sides a, b, and c is scalene; otherwise, returns false"
  [a b c]
  (and (triangle? a b c)
       (not (isosceles? a b c))))
