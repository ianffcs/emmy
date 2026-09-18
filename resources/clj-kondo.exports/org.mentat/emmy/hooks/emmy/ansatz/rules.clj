(ns hooks.emmy.ansatz.rules
  (:require [clj-kondo.hooks-api :as api]))

(defn defruleset
  "`(defruleset name & rules)` defines `name`; the rules are quoted data."
  [{:keys [node]}]
  (let [[_ name-node & rule-nodes] (:children node)]
    {:node (api/list-node
            [(api/token-node 'def)
             name-node
             (api/list-node
              [(api/token-node 'quote)
               (api/list-node (vec rule-nodes))])])}))
