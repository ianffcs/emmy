#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.derivative-test
  (:require [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.derivative :as d]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.polynomial :as polynomial]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.core :as k]))

(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(deftest real-analytic-derivative-laws
  (is (= :installed (d/install!)))
  (doseq [n ["step_ne_zero" "tendsto_congr" "divide_mul_cancel" "unique"
             "const" "id" "add" "neg" "tendsto_step" "reconstruct"
             "tendsto_of_hasDerivAt" "continuousAt" "mul"
             "mul_lt_mul_right" "scale_cancel" "lt_of_mul_lt_mul_right"
             "abs_remainder" "remainder_iff" "comp"]
          :let [label (str "Emmy.Analysis.Derivative." n)
                {:keys [kind statement proof]} (t/declaration label)]]
    (testing n
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? allowed-axioms (t/axioms-of label))))))

(deftest analytic-polynomial-correctness
  (is (= :installed (polynomial/install!)))
  (let [{:keys [statement proof]} (t/declaration polynomial/theorem-name)]
    (is (env/verifies? (k/env) statement proof))
    (is (every? allowed-axioms (t/axioms-of polynomial/theorem-name))))
  (testing "the identity derivative cannot be changed to zero"
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Derivative.id")]
      (is (not (env/verifies? (k/env)
        (t/forall [[x r/R]] (d/has-deriv-at (t/lam "y" r/R identity) r/zero x)) proof))))))

(deftest real-ring-identities
  (r/install!)
  (is (thrown? clojure.lang.ExceptionInfo
        (r/ring-identity! "test_false_ring_identity" '[x] '(* x x) '(+ x x)))))
