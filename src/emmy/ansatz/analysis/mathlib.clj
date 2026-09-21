#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.mathlib
  "Mathlib-shaped compatibility surface for the physlib subset.

  These names are checked aliases/adapters over Emmy.Analysis.Q/R, the generic
  topology layer, and the derivative layer. They do not import Mathlib and do
  not claim full Mathlib coverage."
  (:require [emmy.ansatz.analysis.derivative :as derivative]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.real-topology :as real-topology]
            [emmy.ansatz.analysis.reals :as reals]
            [emmy.ansatz.core :as k]))

(def ^:private prefix "Emmy.Mathlib.")
(def Real reals/R)
(def Rat (k/const "Emmy.Analysis.Q.Q"))
(def MetricSpace (t/arrow t/type0 t/type0))
(def Norm (t/arrow Real Real))
(def Dist (t/arrow Real (t/arrow Real Real)))
(def HasDerivAt (k/const "Emmy.Analysis.Derivative.HasDerivAt"))
(def Continuous (k/const "Emmy.Analysis.R.Continuous"))
(def ContinuousAt (k/const "Emmy.Analysis.R.ContinuousAt"))
(def TendsToAt (k/const "Emmy.Analysis.R.TendsToAt"))

(defn norm [x] (reals/abs x))
(defn dist [x y] (reals/abs (reals/sub x y)))
(defn has-deriv-at [f d x] (derivative/has-deriv-at f d x))
(defn continuous-at [f x] (reals/continuous-at f x))
(defn continuous [f] (reals/continuous f))
(defn tends-to-at [f x L] (reals/tends-to-at f x L))
(defn fderiv
  "One-dimensional Fréchet derivative selected by the derivative witness.
  This is a proposition-valued adapter; uniqueness is checked by the
  derivative layer rather than by choosing a host value."
  [f x d]
  (has-deriv-at f d x))
(defn directional-deriv [f x v d]
  (has-deriv-at (t/lam "s" Real #(t/app f (reals/add x (reals/mul % v)))) d
                reals/zero))

(defn- declare! [name type value]
  (when-not (k/installed? (str prefix name))
    (t/install-declaration! :def (str prefix name) type value)))

(defn install!
  "Installs checked Mathlib-shaped aliases for the physlib analysis subset."
  []
  (locking k/install-lock
    (reals/install!)
    (real-topology/install!)
    (derivative/install!)
    (declare! "Real" t/type0 Real)
    (declare! "Rat" t/type0 Rat)
    (declare! "Norm" (t/arrow Real Real) (t/lam "x" Real norm))
    (declare! "Dist" (t/arrow Real (t/arrow Real Real))
              (t/lam "x" Real #(t/lam "y" Real (fn [y] (dist % y)))))
    (declare! "MetricSpace" (t/arrow t/type0 t/prop)
              (t/lam "A" t/type0 (fn [_] (k/const "True"))))
    (declare! "HasDerivAt" (t/arrow (t/arrow Real Real)
                                     (t/arrow Real (t/arrow Real t/prop)))
              (t/lam "f" (t/arrow Real Real)
                     (fn [f] (t/lam "d" Real (fn [d]
                       (t/lam "x" Real (fn [x] (has-deriv-at f d x))))))))
    (declare! "Continuous" (t/arrow (t/arrow Real Real) t/prop) Continuous)
    (declare! "ContinuousAt" (t/arrow (t/arrow Real Real) (t/arrow Real t/prop))
              ContinuousAt)
    (declare! "TendsToAt" (t/arrow (t/arrow Real Real)
                                    (t/arrow Real (t/arrow Real t/prop)))
              TendsToAt))
  :installed)
