(ns robot-simulator)

(defn robot [pos bearing]
  {:coordinates pos, :bearing bearing})

(def bearings '(:north :east :south :west))

(def bearings-right
  (zipmap bearings (rest (cycle bearings))))

(def bearings-left
  (zipmap (rest (cycle bearings)) bearings))

(defn pos-add [p1 p2] {:x (+ (:x p1) (:x p2))
                       :y (+ (:y p1) (:y p2))})

(defn pos-rotate-right [{:keys [x y]}]
  {:x y, :y (- x)})

(def move-north {:x 0 :y 1})

(def moves "map from bearing to move vector"
  (zipmap bearings (iterate pos-rotate-right move-north)))

(defn step [robot cmd]
  (case cmd 
    \R (update robot :bearing bearings-right)
    \L (update robot :bearing bearings-left)
    \A (update robot :coordinates #(pos-add % (moves (:bearing robot))))))

(defn simulate [cmds robot]
  (reduce step robot cmds))
