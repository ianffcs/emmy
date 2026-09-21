(ns hooks.emmy.ansatz.analysis
  (:require [clj-kondo.hooks-api :as api]))

(defn typed-binders
  "Treat dependent typed binders as sequential bindings for scope analysis."
  [{:keys [node]}]
  (let [[_ bindings body] (:children node)]
    {:node (api/list-node
            [(api/token-node 'let)
             (api/vector-node (vec (mapcat :children (:children bindings))))
             body])}))

(defn with-cont [{:keys [node]}]
  (let [[_ bindings body] (:children node)]
    {:node
     (reduce (fn [tail [params call]]
               (api/list-node
                (conj (vec (:children call))
                      (api/list-node [(api/token-node 'fn) params tail]))))
             body (reverse (partition 2 (:children bindings))))}))
