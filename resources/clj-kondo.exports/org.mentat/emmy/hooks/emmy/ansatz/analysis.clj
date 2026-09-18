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
