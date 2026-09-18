#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.generators
  "test.check generators for polynomial expressions in `x`."
  (:require [clojure.test.check.generators :as gen]
            [emmy.generic :as g]))

(def poly-form
  "Bare Emmy s-expressions for integer polynomials in `x`."
  (gen/recursive-gen
   (fn [inner]
     (gen/one-of
      [(gen/fmap #(cons '+ %) (gen/vector inner 2 3))
       (gen/fmap #(cons '* %) (gen/vector inner 2 3))
       (gen/fmap #(list '- %) inner)
       (gen/fmap #(cons '- %) (gen/vector inner 2))
       (gen/fmap (fn [[b n]] (list 'expt b n))
                 (gen/tuple inner (gen/choose 0 3)))]))
   (gen/one-of [(gen/return 'x)
                (gen/choose -20 20)])))

(defn ->fn
  "The Clojure function of `x` that evaluates `form` with Emmy's generic
  operations. Integer powers are expanded into products (as the Ansatz IR
  does): Emmy's `D` of `(expt u 0)` divides by zero when `u` is 0."
  [form]
  (fn [x]
    (letfn [(walk [f]
              (cond (= 'x f) x
                    (seq? f) (let [[op & args] f
                                   args (map walk args)]
                               (case op
                                 + (apply g/+ args)
                                 * (apply g/* args)
                                 - (apply g/- args)
                                 expt (let [[b n] args]
                                        (reduce g/* 1 (repeat n b)))))
                    :else f))]
      (walk form))))
