(ns cars-assemble)

(defn success-rate [speed]
  (cond (== speed 0) 0
        (<= speed 4) 1
        (<= speed 8) 0.9
        (== speed 9) 0.8
        (== speed 10) 0.77))

(defn production-rate
  "Returns the assembly line's production rate per hour,
   taking into account its success rate"
  [speed]
  (* 221 speed (success-rate speed)))

(defn working-items
  "Calculates how many working cars are produced per minute"
  [speed]
  (int (/ (production-rate speed) 60)))
