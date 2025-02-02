(ns triangle)

(defn triangle? [& sides]
  (let [sum (reduce + sides)
        m (reduce max sides)]
    (and (every? pos? sides)
         (<= m (- sum m)))))

(defn equilateral?
  "Returns true if the triangle with sides a, b, and c is equilateral; otherwise, returns false"
  [a b c]
  (and (pos? a) (= a b c)))

(defn isosceles?
  "Returns true if the triangle with sides a, b, and c is isosceles; otherwise, returns false"
  [a b c]
  (and (triangle? a b c)
       (not (distinct? a b c))))

(defn scalene?
  "Returns true if the triangle with sides a, b, and c is scalene; otherwise, returns false"
  [a b c]
  (and (triangle? a b c)
       (distinct? a b c)))
