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
        (t/pi "U" set-a
              (fn [v] (t/pi "V" set-a
                            (fn [w]
                              (t/arrow (t/app o v)
                                       (t/arrow (t/app o w)
                                                (t/app o (t/lam "x" a
                                                                #(t/and' (t/app v %) (t/app w %))))))))))
        unions
        (t/pi "family" (t/predicate set-a)
              (fn [family]
                (t/arrow
                 (t/pi "U" set-a #(t/arrow (t/app family %) (t/app o %)))
                 (t/app o
                        (t/lam "x" a
                               (fn [x]
                                 (t/exists' set-a
                                            (t/lam "U" set-a
                                                   #(t/and' (t/app family %) (t/app % x))))))))))]
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
       (t/pi "A" t/type0
             (fn [a] (t/pi "B" t/type0
                           #(t/arrow (space a) (t/arrow (space %) (t/arrow (t/arrow a %) t/prop))))))
       (t/lam "A" t/type0
              (fn [a]
                (t/lam "B" t/type0
                       (fn [b]
                         (t/lam "source" (space a)
                                (fn [sa]
                                  (t/lam "target" (space b)
                                         (fn [sb]
                                           (t/lam "f" (t/arrow a b)
                                                  (fn [f]
                                                    (t/pi "U" (t/predicate b)
                                                          (fn [v]
                                                            (t/arrow (t/app (opens b sb) v)
                                                                     (t/app (opens a sa)
                                                                            (t/lam "x" a #(t/app v (t/app f %)))))))))))))))))))
    (when-not (k/installed? (str prefix "continuous_id"))
      (t/install-declaration!
       :thm (str prefix "continuous_id")
       (t/pi "A" t/type0
             (fn [a] (t/pi "space" (space a)
                           #(continuous a a % % (t/lam "x" a identity)))))
       (t/lam "A" t/type0
              (fn [a] (t/lam "space" (space a)
                            (fn [sa] (t/lam "U" (t/predicate a)
                                            #(t/lam "open" (t/app (opens a sa) %) identity))))))))
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
