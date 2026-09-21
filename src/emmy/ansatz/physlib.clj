#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.physlib
  "A small Emmy-facing, physlib-shaped interface over verified rational
  polynomials.

  `time-deriv` and `space-deriv` have the same operational interpretation as
  physlib's coordinate derivatives: parameters not selected as the coordinate
  are held fixed. The derivative, including rational coefficients, is
  verified in Ansatz. `derivative-proof` supplies the analytic HasDerivAt
  statement over constructed reals; approximate evaluation remains separate.
  This is a coordinate-polynomial interface, not an upstream physlib import."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.lagrange :as lagrange]
            [emmy.ansatz.analysis.polynomial :as polynomial]
            [emmy.ansatz.calculus :as calculus]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as expression]
            [emmy.ansatz.simplify :as simplify]
            [emmy.expression :as x]))

(defn- proof-input [expr var]
  (when-not (symbol? var)
    (throw (ex-info "The coordinate must be a symbol" {:variable var})))
  (k/ensure-init!)
  (when-not (k/installed? polynomial/theorem-name) (polynomial/install!))
  (let [ir     (expression/->ir expr)
        params (expression/params-of ir var)
        value  (expression/ir->value ir var params)]
    {:params params
     :term   (polynomial/value->term value)}))

(defn derivative-proof
  "Returns a kernel proof of the polynomial's analytic derivative over ℝ.
  The closed statement quantifies every real coordinate x and parameter
  environment rho. `:params` assigns symbols to rho's natural-number indices.
  No approximate numeric values are involved."
  ([expr] (derivative-proof expr 'x))
  ([expr var]
   (let [{:keys [params term]} (proof-input expr var)
         statement (polynomial/proposition term)
         proof (t/app (k/const polynomial/theorem-name) term)]
     (when-not (env/verifies? (k/env) statement proof)
       (throw (ex-info "Kernel rejected polynomial derivative proof" {:expression expr})))
     {:expression (x/expression-of expr)
      :variable   var
      :params     params
      :statement  statement
      :proof      proof})))

(defn derivative-proof?
  "Checks the proof against the full statement AND reconstructs the expected
  statement from the expression and coordinate. Forged metadata is not evidence."
  [{:keys [expression variable params statement proof]}]
  (boolean
   (try
     (when (and statement proof)
       (let [{expected-params :params term :term} (proof-input expression variable)
             expected (polynomial/proposition term)
             u (level/succ level/zero)]
         (and (= params expected-params)
              (env/verifies? (k/env) statement proof)
              (env/verifies? (k/env)
                (k/eq-at t/prop u expected statement)
                (:term (k/refl expected t/prop u))))))
     (catch Exception _ false))))

(declare approximate-value)

(defn polynomial-derivative-report
  "Reports approximate polynomial and derivative values. This is diagnostic
  data, not a proof or a certificate of an analytic derivative."
  ([expr x] (polynomial-derivative-report expr 'x x))
  ([expr var x]
   (let [poly (expression/->poly-expr expr var)
         deriv (calculus/deriv-poly poly)
         deriv (simplify/simp-poly deriv)]
     {:kind            ::polynomial-derivative-report
      :at              x
      :poly            poly
      :derivative      deriv
      :certified?      false
      :theorem         calculus/theorem-name
      :value           (approximate-value poly x)
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

(def ^:private lagrange-theorems
  {:free-particle-momentum
   {:name "Emmy.Analysis.Lagrange.kinetic_momentum"
    :reading "d/dv (½·m·v²) = m·v: the free particle's momentum is derived, not assumed."}
   :free-particle-force
   {:name "Emmy.Analysis.Lagrange.kinetic_force"
    :reading "∂/∂q (½·m·v²) = 0: the free Lagrangian does not depend on position."}
   :momentum-derivative
   {:name "Emmy.Analysis.Lagrange.momentum_deriv"
    :reading "d/dt (m·v t) = m·a whenever the velocity has derivative a."}
   :uniform-motion
   {:name "Emmy.Analysis.Lagrange.free_particle_uniform"
    :reading "A path with zero acceleration satisfies d/dt (∂L/∂v) = ∂L/∂q for L = ½·m·v²."}})

(defn lagrange-proof
  "Returns the installed kernel theorem backing one Euler–Lagrange fact,
  checked against its own statement before being handed back. `which` is one of
  the keys of [[lagrange-facts]]. This is a proof term, not a numeric result."
  [which]
  (let [{:keys [name reading]} (or (get lagrange-theorems which)
                                   (throw (ex-info "Unknown Euler–Lagrange fact"
                                                   {:requested which
                                                    :available (sort (keys lagrange-theorems))})))]
    (k/ensure-init!)
    (lagrange/install!)
    (let [{:keys [statement proof]} (t/declaration name)]
      (when-not (env/verifies? (k/env) statement proof)
        (throw (ex-info "Kernel rejected Euler–Lagrange proof" {:theorem name})))
      {:fact which :theorem name :reading reading :statement statement :proof proof})))

(defn lagrange-facts
  "The Euler–Lagrange facts [[lagrange-proof]] can supply, with their readings."
  []
  (into (sorted-map)
        (map (fn [[k v]] [k (:reading v)])) lagrange-theorems))

(defn approximate-value
  "Evaluates using double arithmetic, without a certified error bound.
  `params` are ordered as
  [[emmy.ansatz.expression/params-of]] orders the non-coordinate symbols."
  ([poly x] (expression/eval-real-poly poly x))
  ([poly x params] (expression/eval-real-poly poly x params)))
