#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.physlib
  "A small Emmy-facing, physlib-shaped interface over verified rational
  polynomials.

  `time-deriv` and `space-deriv` have the same operational interpretation as
  physlib's coordinate derivatives: parameters not selected as the coordinate
  are held fixed. The integer numerator derivative is verified in Ansatz;
  rational wrapping is host-side glue. Approximate evaluation uses doubles,
  not constructed reals or analytic `HasDerivAt` certification."
  (:require [emmy.ansatz.calculus :as calculus]
            [emmy.ansatz.expression :as expression]
            [emmy.ansatz.simplify :as simplify]))

(declare approximate-value)

(defn polynomial-derivative-report
  "Reports approximate polynomial and derivative values. This is diagnostic
  data, not a proof or a certificate of an analytic derivative."
  ([expr x] (polynomial-derivative-report expr 'x x))
  ([expr var x]
   (let [poly (expression/->poly-expr expr var)
         deriv (calculus/deriv-poly poly)
         deriv (if (map? deriv) (update deriv :numerator simplify/simp-poly)
                   (simplify/simp-poly deriv))]
     {:kind ::polynomial-derivative-report :at x :poly poly :derivative deriv
      :certified? false
      :theorem calculus/theorem-name
      :value (approximate-value poly x)
      :derivative-value (approximate-value deriv x)})))

(defn time-deriv
  "Coordinate derivative with respect to `t` (default `t`), analogous to
  physlib's `Time.deriv`."
  ([f] (time-deriv f 't))
  ([f t] (calculus/derivative f t)))

(defn space-deriv
  "Derivative in coordinate `mu` of an `n`-argument function, analogous to
  physlib's basis-direction `Space.deriv`."
  ([mu f] (space-deriv mu f 1))
  ([mu f n] (calculus/partial-derivative f mu n)))

(defn gradient
  "The coordinate gradient of `f`, matching physlib's repeated space-deriv
  convention for the supplied argument count."
  [f n]
  (calculus/gradient f n))

(defn approximate-value
  "Evaluates using double arithmetic, without a certified error bound.
  `params` are ordered as
  [[emmy.ansatz.expression/params-of]] orders the non-coordinate symbols."
  ([poly x] (expression/eval-real-poly poly x))
  ([poly x params] (expression/eval-real-poly poly x params)))
