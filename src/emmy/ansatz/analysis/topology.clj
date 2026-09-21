#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.topology
  "Open-set topology in the Ansatz kernel, independent of Mathlib.
  Spaces have empty/universal opens and closure under binary intersections and
  arbitrary unions. Continuity is preservation of opens under inverse image.
  The real instance is installed by `analysis.real-topology`."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]))

(def ^:private u (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.Topology.")
(defn- c [s] (k/const (str prefix s)))
(defn space
  "The type of topologies on `a`."
  [a]
  (t/app (c "Space") a))

(defn opens
  "The open-set predicate of a space."
  [a s]
  (t/app (c "IsOpen") a s))

(defn continuous
  "Continuity by open inverse images."
  [a b sa sb f]
  (t/app (c "Continuous") a b sa sb f))

(defn- laws [a o]
  (let [set-a (t/predicate a)
        empty-set (t/lam "x" a (fn [_] (k/const "False")))
        full-set (t/lam "x" a (fn [_] (k/const "True")))
        intersections
        (t/forall [[v set-a] [w set-a]]
          (t/>-> (t/app o v)
                 (t/app o w)
                 (t/app o (t/lambda [[x a]]
                            (t/and' (t/app v x) (t/app w x))))))
        unions
        (t/forall [[family (t/predicate set-a)]]
          (t/arrow
           (t/forall [[v set-a]] (t/arrow (t/app family v) (t/app o v)))
           (t/app o
             (t/lambda [[x a]]
               (t/exists' set-a
                 (t/lambda [[v set-a]]
                   (t/and' (t/app family v) (t/app v x))))))))]
    (t/and' (t/app o empty-set)
            (t/and' (t/app o full-set) (t/and' intersections unions)))))

(defn- space-predicate [a]
  (t/lam "opens" (t/predicate (t/predicate a)) #(laws a %)))

(defn space-intro
  "Constructs a space from an open predicate and proofs of the four axioms.
  Arguments: empty open, universal open, binary intersections, arbitrary unions."
  [a o empty-open full-open intersections unions]
  (let [axioms (laws a o)
        ;; Build the nested conjunction using its explicit argument types.
        parts (fn [p] (second (e/get-app-fn-args p)))
        [p rest1] (parts axioms)
        [q rest2] (parts rest1)
        [r s] (parts rest2)]
    (t/app (k/const "Subtype.mk" u) (t/predicate (t/predicate a)) (space-predicate a) o
           (t/and-intro p rest1 empty-open
                        (t/and-intro q rest2 full-open
                                     (t/and-intro r s intersections unions))))))

(defn install!
  "Installs the space and continuity definitions and checked identity and
  composition theorems. Returns :installed; requires only bundled Init."
  []
  (k/ensure-init!)
  (locking k/install-lock
    (when-not (k/installed? (str prefix "Space"))
      (t/install-declaration!
       :def (str prefix "Space") (t/arrow t/type0 t/type0)
       (t/lam "A" t/type0
              #(t/app (k/const "Subtype" u)
                      (t/predicate (t/predicate %)) (space-predicate %)))))
    (when-not (k/installed? (str prefix "IsOpen"))
      (t/install-declaration!
       :def (str prefix "IsOpen")
       (t/pi "A" t/type0 #(t/arrow (space %) (t/predicate (t/predicate %))))
       (t/lam "A" t/type0
              (fn [a]
                (t/lam "space" (space a)
                       #(t/app (k/const "Subtype.val" u)
                               (t/predicate (t/predicate a)) (space-predicate a) %))))))
    (when-not (k/installed? (str prefix "Continuous"))
      (t/install-declaration!
       :def (str prefix "Continuous")
       (t/forall [[a t/type0] [b t/type0]]
         (t/>-> (space a) (space b) (t/arrow a b) t/prop))
       (t/lambda [[a t/type0] [b t/type0]
                  [source (space a)] [target (space b)] [f (t/arrow a b)]]
         (t/forall [[v (t/predicate b)]]
           (let [preimage (t/lambda [[x a]] (t/app v (t/app f x)))]
             (t/arrow (t/app (opens b target) v)
                      (t/app (opens a source) preimage)))))))
    (when-not (k/installed? (str prefix "continuous_id"))
      (t/install-declaration!
       :thm (str prefix "continuous_id")
       (t/forall [[a t/type0] [sa (space a)]]
         (continuous a a sa sa (t/lambda [[x a]] x)))
       (t/lambda [[a t/type0] [sa (space a)]
                  [v (t/predicate a)] [hv (t/app (opens a sa) v)]]
         hv)))
    (when-not (k/installed? (str prefix "continuous_comp"))
      (t/install-declaration!
       :thm (str prefix "continuous_comp")
       (t/forall [[a t/type0] [b t/type0] [c t/type0]
                  [sa (space a)] [sb (space b)] [sc (space c)]
                  [f (t/arrow a b)] [g (t/arrow b c)]]
         (t/arrow (continuous a b sa sb f)
                  (t/arrow (continuous b c sb sc g)
                           (continuous a c sa sc
                                       (t/lambda [[x a]] (t/app g (t/app f x)))))))
       (t/lambda [[a t/type0] [b t/type0] [c t/type0]
                  [sa (space a)] [sb (space b)] [sc (space c)]
                  [f (t/arrow a b)] [g (t/arrow b c)]
                  [hf (continuous a b sa sb f)]
                  [hg (continuous b c sb sc g)]
                  [v (t/predicate c)] [hv (t/app (opens c sc) v)]]
         (t/app hf (t/lambda [[y b]] (t/app v (t/app g y))) (t/app hg v hv))))))
  :installed)
