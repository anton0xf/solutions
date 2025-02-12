(ns card-games)

(defn rounds
  "Takes the current round number and returns 
   a `list` with that round and the _next two_."
  [n]
  (range n (+ n 3)))

(defn concat-rounds 
  "Takes two lists and returns a single `list` 
   consisting of all the rounds in the first `list`, 
   followed by all the rounds in the second `list`"
  [l1 l2]
  (concat l1 l2))

(defn contains-round? 
  "Takes a list of rounds played and a round number.
   Returns `true` if the round is in the list, `false` if not."
  [l n]
  (.contains l n))

(defn card-average
  "Returns the average value of a hand"
  [hand]
  (/ (reduce + 0.0 hand) (count hand)))

(defn approx-average?
  "Returns `true` if average is equal to either one of:
  - Take the average of the _first_ and _last_ number in the hand.
  - Using the median (middle card) of the hand."
  [hand]
  (let [a (card-average hand)
        a1 (/ (+ (first hand) (last hand)) 2.0)
        a2 (float (nth hand (quot (count hand) 2)))]
    (or (= a a1) (= a a2))))

(defn average-even-odd?
  "Returns true if the average of the cards at even indexes 
   is the same as the average of the cards at odd indexes."
  [hand]
  (let [a (card-average hand)
        indexed-hand (map vector (range) hand)
        a1 (->> indexed-hand
                (filter #(odd? (first %)))
                (map second)
                card-average) 
        a2 (->> indexed-hand
                (filter #(even? (first %)))
                (map second)
                card-average)]
    (or (= a a1) (= a a2))))

(defn maybe-double-last
  "If the last card is a Jack (11), doubles its value
   before returning the hand."
  [hand]
  (let [card (last hand)]
    (if (= 11 card)
      (concat (butlast hand) [(* 2 card)])
      hand)))
