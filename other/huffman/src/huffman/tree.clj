(ns huffman.tree)

;; tree = nil | char | [tree tree]
(defn make-tree [nodes]
  (loop [nodes nodes
         stack '()]
    (cond (empty? nodes) (first stack)

          (= "C" (first nodes))
          (recur (rest nodes)
                 (conj (drop 2 stack) [(second stack) (first stack)]))

          (= \P (first (first nodes)))
          (recur (rest nodes)
                 (conj stack (second (first nodes))))

          :else (throw (ex-info "unexpected node" (first nodes))))))

(defn encode-tree [tree]
  (cond (nil? tree) nil
        (char? tree) [[tree nil]]
        :else (mapcat (fn [code encoded]
                        (map (fn [[ch s]] [ch (cons code s)]) encoded))
                      [\0 \1]
                      (map encode-tree tree))))
