#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.mathlib
  "Mathlib-shaped compatibility surface for the physlib subset.

  These names are checked aliases/adapters over Emmy.Analysis.Q/R, the generic
  topology layer, and the derivative layer. They do not import Mathlib and do
  not claim full Mathlib coverage."
  (:require [clojure.string :as string]
            [emmy.ansatz.analysis.derivative :as derivative]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.metric :as metric]
            [emmy.ansatz.analysis.real-topology :as real-topology]
            [emmy.ansatz.analysis.reals :as reals]
            [emmy.ansatz.core :as k]))

(def ^:private prefix "Emmy.Mathlib.")
(def Real reals/R)
(def Rat (k/const "Emmy.Analysis.Q.Q"))
;; The checked metric-space structure, exported from the underlying analysis
;; namespace rather than reintroducing the old inhabited-`True` placeholder.
(def MetricSpace (k/const "Emmy.Analysis.Metric.MetricSpace"))
(def Norm (t/>-> Real Real))
(def Dist (t/>-> Real Real Real))
(def HasDerivAt (k/const "Emmy.Analysis.Derivative.HasDerivAt"))
(def Continuous (k/const "Emmy.Analysis.R.Continuous"))
(def ContinuousAt (k/const "Emmy.Analysis.R.ContinuousAt"))
(def TendsToAt (k/const "Emmy.Analysis.R.TendsToAt"))

(defn norm [x]
  (reals/abs x))

(defn dist [x y]
  (reals/abs (reals/sub x y)))

(defn has-deriv-at [f d x]
  (derivative/has-deriv-at f d x))

(defn continuous-at [f x]
  (reals/continuous-at f x))

(defn continuous [f]
  (reals/continuous f))

(defn tends-to-at [f x L]
  (reals/tends-to-at f x L))
(defn ^{:deprecated "Use has-deriv-at; retained only for migration."} derivative-witness
  "Deprecated proposition-valued one-dimensional derivative adapter.

  This is intentionally not called `fderiv`: it does not compute or select a
  Fréchet derivative value."
  [f x d]
  (has-deriv-at f d x))
(defn directional-deriv [f x v d]
  (let [line (t/lam "s" Real
                    #(t/app f (reals/add x (reals/mul % v))))]
    (has-deriv-at line d reals/zero)))

(def ^:private decl (t/declarer prefix))

(defn- reject-stale-metric-space
  "Pure. Throws if `ctx` already carries an `Emmy.Mathlib.MetricSpace`
  declaration that doesn't match the checked structure alias -- the Ansatz
  environment is process-global, so a previous process may have left the old
  inhabited-`True` placeholder behind, and `decl` would otherwise silently
  leave it in place since it's idempotent."
  [ctx]
  (when-let [{:keys [statement proof]} (t/declaration ctx (str prefix "MetricSpace"))]
    (let [expected-type (t/>-> t/type0 t/prop)]
      ;; Lambda binders carry fresh fvar ids, so compare the stable declaration
      ;; shape rather than a newly-built lambda for alpha-equivalence.
      (when (or (not= statement expected-type)
                (not (string/includes?
                      (pr-str proof) "Emmy.Analysis.Metric.MetricSpace")))
        (throw (ex-info "Stale Emmy.Mathlib.MetricSpace declaration"
                        {:name (str prefix "MetricSpace")}))))))

(defn install
  "Pure. Declares this namespace's checked Mathlib-shaped aliases into `ctx`."
  [ctx]
  (reject-stale-metric-space ctx)
  (-> ctx
      (decl :def "Real" t/type0 Real)
      (decl :def "Rat" t/type0 Rat)
      (decl :def "Norm" (t/>-> Real Real) (t/lam "x" Real norm))
      (decl :def "Dist" (t/>-> Real Real Real)
            (t/lam "x" Real #(t/lam "y" Real (fn [y] (dist % y)))))
      (decl :def "MetricSpace" (t/>-> t/type0 t/prop)
            (t/lam "A" t/type0 (fn [a] (t/app MetricSpace a))))
      (decl :def "HasDerivAt" (t/>-> (t/>-> Real Real) Real Real t/prop)
            (t/lam "f" (t/arrow Real Real)
                   (fn [f] (t/lam "d" Real
                             (fn [d] (t/lam "x" Real (fn [x] (has-deriv-at f d x))))))))
      (decl :def "Continuous" (t/>-> (t/>-> Real Real) t/prop) Continuous)
      (decl :def "ContinuousAt" (t/>-> (t/>-> Real Real) Real t/prop) ContinuousAt)
      (decl :def "TendsToAt" (t/>-> (t/>-> Real Real) Real Real t/prop) TendsToAt)))

(defn install!
  "Installs checked Mathlib-shaped aliases for the physlib analysis subset."
  []
  (locking k/install-lock
    (k/ensure-init!)
    (reals/install!)
    (real-topology/install!)
    (derivative/install!)
    (metric/install!)
    (k/commit! install))
  :installed)
