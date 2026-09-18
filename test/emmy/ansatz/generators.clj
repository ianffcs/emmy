#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.generators
  "test.check generators for polynomial expressions in `x`."
  (:require [clojure.test.check.generators :as gen]
            [emmy.generic :as g]))

(defn poly-form-over
  "Bare Emmy s-expressions for integer polynomials in the symbols `syms`."
  [syms]
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of
      [(gen/fmap #(cons '+ %) (gen/vector inner 2 3))
       (gen/fmap #(cons '* %) (gen/vector inner 2 3))
       (gen/fmap #(list '- %) inner)
       (gen/fmap #(cons '- %) (gen/vector inner 2))
       (gen/fmap (fn [[b n]] (list 'expt b n))
                 (gen/tuple inner (gen/choose 0 3)))]))
   (gen/one-of [(gen/elements syms)
                (gen/choose -20 20)])))

(def poly-form
  "Bare Emmy s-expressions for integer polynomials in `x`."
  (poly-form-over ['x]))

(defn ->fn-of
  "The Clojure function of the symbols `syms` that evaluates `form` with Emmy's
  generic operations. Integer powers are expanded into products (as the
  Ansatz IR does): Emmy's `D` of `(expt u 0)` divided by zero when `u` was 0
  before the fix in `emmy.generic`, and products keep the comparison
  independent of `expt`'s derivative rule."
  [syms form]
  (fn [& args]
    (let [env (zipmap syms args)]
      (letfn [(walk [f]
                (cond (contains? env f) (env f)
                      (seq? f) (let [[op & args] f
                                     args (map walk args)]
                                 (case op
                                   + (apply g/+ args)
                                   * (apply g/* args)
                                   - (apply g/- args)
                                   expt (let [[b n] args]
                                          (reduce g/* 1 (repeat n b)))))
                      :else f))]
        (walk form)))))

(defn ->fn
  "The Clojure function of `x` that evaluates `form` (see [[->fn-of]])."
  [form]
  (->fn-of ['x] form))
