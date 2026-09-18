#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.kernel
  "Typed term builders for the independent analysis library.
  Every new definition and theorem passes through check-constant. No axiom
  constructor or unchecked environment insertion is exposed here."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [emmy.ansatz.core :as k]))

(def type0 (e/sort' (level/succ level/zero)))
(def prop (e/sort' level/zero))
(defonce ^:private ids (atom 8000000000))

(defn pi [label domain body]
  (let [id (swap! ids inc)]
    (e/forall' label domain (e/abstract1 (body (e/fvar id)) id) :default)))

(defn lam [label domain body]
  (let [id (swap! ids inc)]
    (e/lam label domain (e/abstract1 (body (e/fvar id)) id) :default)))

(defmacro forall
  "Constructs nested dependent function types from [symbol type] bindings."
  [bindings body]
  (reduce (fn [body [sym domain]] `(pi ~(str sym) ~domain (fn [~sym] ~body)))
          body (reverse bindings)))

(defmacro lambda
  "Constructs nested typed lambda terms from [symbol type] bindings."
  [bindings body]
  (reduce (fn [body [sym domain]] `(lam ~(str sym) ~domain (fn [~sym] ~body)))
          body (reverse bindings)))

(defn arrow [a b] (e/arrow a b))
(defn app [f & xs] (apply e/app* f xs))
(defn predicate [a] (arrow a prop))
(defn and' [a b] (app (k/const "And") a b))
(defn exists' [a p] (app (k/const "Exists" (level/succ level/zero)) a p))

(defn install-declaration!
  "Checks a closed definition or theorem and installs it atomically.
  Existing declarations are rejected rather than silently trusted."
  [kind label type value]
  (when-not (#{:def :thm} kind)
    (throw (ex-info "Only checked definitions and theorems are permitted" {:kind kind})))
  (when (or (nil? type) (nil? value))
    (throw (ex-info "A declaration requires both a type and a value" {:name label})))
  (k/ensure-init!)
  (locking k/install-lock
    (let [constructor (case kind :def env/mk-def :thm env/mk-thm)
          ci (constructor (name/from-string label) [] type value)]
      (swap! a/ansatz-env #(env/check-constant % ci))))
  (k/const label))

(defn declaration
  "Returns an installed declaration with its complete type and value."
  [label]
  (when-let [ci (env/lookup (k/env) (name/from-string label))]
    {:kind (env/ci-tag ci) :statement (env/ci-type ci) :proof (env/ci-value ci)}))
