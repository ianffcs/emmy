#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.metric
  "Checked metric-space vocabulary for the Ansatz analysis library.

  A metric is represented by its distance function together with the four
  laws needed by the ε–δ development: self distance, symmetry, separation,
  and the strict triangle estimate.  The strict triangle form is the useful
  one for this library because it composes directly with the existing real
  ε–δ proofs.

  The real instance uses `abs (x - y)`.  Its open balls have the same
  predicate as `Emmy.Analysis.RealTopology.Ball`, so the metric and open-set
  interfaces can be used together without an unchecked bridge."
  (:require [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.analysis.topology :as topology]
            [emmy.ansatz.core :as k]))

(def ^:private prefix "Emmy.Analysis.Metric.")
(def ^:private u (level/succ level/zero))
(defn- c [name] (k/const (str prefix name)))
(def ^:private R r/R)
(def ^:private Prop t/prop)

(defn distance-type
  "The type of real-valued distances on a carrier `a`."
  [a]
  (t/>-> a a R))

(defn distance
  "Apply a metric distance function to two points."
  [d x y]
  (t/app d x y))

(defn metric-laws
  "The proposition expressing the checked metric laws for `d : Dist a`."
  [a d]
  (let [dist #(distance d %1 %2)]
    (t/and'
     (t/forall [[x a]] (k/eq-at R u (dist x x) r/zero))
     (t/and'
      (t/forall [[x a] [y a]]
        (k/eq-at R u (dist x y) (dist y x)))
      (t/and'
       (t/forall [[x a] [y a]]
         (t/>-> (t/not' (k/eq-at a u x y))
                (r/lt r/zero (dist x y))))
       (t/forall [[x a] [y a] [z a] [eps R] [delta R]]
         (t/>-> (r/lt (dist x y) eps)
                (r/lt (dist y z) delta)
                (r/lt (dist x z) (r/add eps delta)))))))))

(defn metric-space
  "The proposition that `a` admits a real-valued metric distance."
  [a]
  (t/forall [[d (distance-type a)]] (metric-laws a d)))

(defn ball
  "The open ball of radius `eps` around `center` for `d`."
  [a d center eps]
  (t/lam "y" a (fn [y] (r/lt (distance d y center) eps))))

(defn metric-is-open
  "The ε-ball definition of openness for a distance function."
  [a d set]
  (t/forall [[x a]]
    (t/>-> (t/app set x)
           (t/exists' R
             (t/lambda [[eps R]]
               (t/and' (r/lt r/zero eps)
                       (t/forall [[y a]]
                         (t/>-> (r/lt (distance d y x) eps)
                                (t/app set y)))))))))

(defn real-distance
  "The constructed-real distance `|x - y|`."
  [x y]
  (r/abs (r/sub x y)))

(def real-metric-distance
  "The real distance function as a kernel term."
  (t/lam "x" R (fn [x] (t/lam "y" R (fn [y] (real-distance x y))))))

(defn- eq-refl [type x]
  (t/app (k/const "Eq.refl" u) type x))

(defn- real-laws-proof []
  (let [d real-metric-distance
        dist #(distance d %1 %2)
        self (t/forall [[x R]] (k/eq-at R u (dist x x) r/zero))
        comm (t/forall [[x R] [y R]] (k/eq-at R u (dist x y) (dist y x)))
        sep (t/forall [[x R] [y R]]
              (t/>-> (t/not' (k/eq-at R u x y))
                     (r/lt r/zero (dist x y))))
        triangle (t/forall [[x R] [y R] [z R] [eps R] [delta R]]
                   (t/>-> (r/lt (dist x y) eps)
                          (r/lt (dist y z) delta)
                          (r/lt (dist x z) (r/add eps delta))))
        rest1 (t/and' comm (t/and' sep triangle))]
    (t/and-intro self rest1
     (t/lambda [[x R]]
       (t/app (k/const "Eq.trans" u) R (dist x x) (r/abs (r/sub x x)) r/zero
              (eq-refl R (dist x x))
              (t/app (k/const "Emmy.Analysis.R.abs_sub_self") x)))
     (t/and-intro comm (t/and' sep triangle)
      (t/lambda [[x R] [y R]]
       (t/app (k/const "Emmy.Analysis.R.abs_sub_comm") x y))
      (t/and-intro sep triangle
       (t/lambda [[x R] [y R] [hne (t/not' (k/eq-at R u x y))]]
         (t/app (k/const "Emmy.Analysis.R.abs_pos_of_ne") x y hne))
       (t/lambda [[x R] [y R] [z R] [eps R] [delta R]
                  [hxy (r/lt (dist x y) eps)]
                  [hyz (r/lt (dist y z) delta)]]
         (t/app (k/const "Emmy.Analysis.R.dist_triangle_lt") x y z eps delta hxy hyz)))))))

(def ^:private decl (t/declarer prefix))

(defn install
  "Pure. Declares checked metric definitions and the constructed-real
  instance into `ctx`."
  [ctx]
  (-> ctx
      (decl :def "Distance" (t/>-> t/type0 t/type0)
            (t/lam "A" t/type0 distance-type))
      (decl :def "MetricSpace" (t/>-> t/type0 Prop)
            (t/lam "A" t/type0 metric-space))
      (decl :def "Ball"
            (t/forall [[a t/type0]]
              (t/>-> (distance-type a) a R (t/predicate a)))
            (t/lam "A" t/type0
                   (fn [a]
                     (t/lam "d" (distance-type a)
                            (fn [d]
                              (t/lam "center" a
                                     (fn [center]
                                       (t/lam "eps" R
                                              (fn [eps]
                                                (t/lam "y" a
                                                       (fn [y]
                                                         (r/lt (distance d y center) eps))))))))))))
      (decl :def "IsOpen"
            (t/forall [[a t/type0]]
              (t/>-> (distance-type a) (t/predicate a) Prop))
            (t/lam "A" t/type0
                   (fn [a]
                     (t/lam "d" (distance-type a)
                            (fn [d]
                              (t/lam "set" (t/predicate a)
                                     (fn [set] (metric-is-open a d set))))))))
      (decl :def "realDistance" (distance-type R) real-metric-distance)
      (decl :thm "realMetricLaws" (metric-laws R real-metric-distance) (real-laws-proof))))

(defn install!
  "Install checked metric definitions and the constructed-real instance."
  []
  (locking k/install-lock
    (r/install!)
    (topology/install!)
    (k/commit! install))
  :installed)
