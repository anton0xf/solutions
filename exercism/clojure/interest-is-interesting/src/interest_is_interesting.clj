(ns interest-is-interesting)

(defn interest-rate
  "Returns the interest rate based on the specified balance."
  [balance]
  (cond
    (neg? balance) -3.213
    (< balance 1000) 0.5
    (< balance 5000) 1.621
    :else 2.475))

(defn annual-balance-update
  "Returns the annual balance update, taking into account the interest rate."
  [balance]
  (+ balance (* (abs balance)
                (bigdec (/ (interest-rate balance) 100)))))

(defn round-down [^BigDecimal n]
  (.intValue (.setScale n 0 java.math.RoundingMode/DOWN)))

(defn amount-to-donate
  "Returns how much money to donate based on the balance and the tax-free percentage."
  [balance tax-free-percentage]
  (if (neg? balance) 0
      (round-down (* balance (bigdec (/ tax-free-percentage 100)) 2))))

