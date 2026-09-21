#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.lagrange-test
  (:require [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.derivative :as d]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.lagrange :as lg]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.core :as k]))

(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(def ^:private theorems
  ["update_same" "update_other" "update_self" "hasDerivAt_congr"
   "partial_const" "partial_proj_same" "partial_proj_other" "partial_add"
   "curve_const" "curve_add"
   "scale" "kinetic_momentum" "kinetic_force" "momentum_deriv"
   "free_particle_uniform"])

(def ^:private definitions
  ["update" "HasPartialDerivAt" "HasCurveDerivAt" "ELPath"])

(deftest finite-dimensional-and-lagrange
  (is (= :installed (lg/install!)))
  (is (= :installed (lg/install!)) "idempotent")
  (doseq [n definitions]
    (is (= :def (:kind (t/declaration (str "Emmy.Analysis.Lagrange." n)))) n))
  (doseq [n theorems
          :let [label (str "Emmy.Analysis.Lagrange." n)
                {:keys [kind statement proof]} (t/declaration label)]]
    (testing n
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? allowed-axioms (t/axioms-of label))))))

(deftest false-claims-are-rejected
  (lg/install!)
  (testing "the coordinate partial is 1, not 0"
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Lagrange.partial_proj_same")]
      (is (not (env/verifies?
                (k/env)
                (t/forall [[i lg/Nat] [p lg/Pt]]
                  (lg/has-partial (t/lam "q" lg/Pt #(t/app % i)) i r/zero p))
                proof)))))
  (testing "a different coordinate's partial needs the distinctness hypothesis"
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Lagrange.partial_proj_other")]
      (is (not (env/verifies?
                (k/env)
                (t/forall [[i lg/Nat] [j lg/Nat] [p lg/Pt]]
                  (lg/has-partial (t/lam "q" lg/Pt #(t/app % j)) i r/zero p))
                proof)))))
  (testing "the free particle's momentum is m·v, not v"
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Lagrange.kinetic_momentum")]
      (is (not (env/verifies?
                (k/env)
                (t/forall [[m r/R] [v r/R]]
                  (d/has-deriv-at (t/lam "w" r/R #(r/mul (r/mul r/half m) (r/mul % %))) v v))
                proof))))))
