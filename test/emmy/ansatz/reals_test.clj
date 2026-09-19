#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.reals-test
  (:require [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.core :as k]))

(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(def ^:private theorems
  ["equiv_refl" "equiv_symm" "equiv_trans" "const_cauchy" "add_cauchy" "neg_cauchy"
   "add_congr" "neg_congr"])

(def ^:private definitions
  ["Cauchy" "CSeq" "Equiv" "R" "constSeq" "ofQ" "addSeq" "negSeq" "cadd" "cneg"
   "add" "neg" "sub" "zero" "one"])

(deftest cauchy-reals
  (is (= :installed (r/install!)))
  (is (= :installed (r/install!)) "idempotent")
  (doseq [n definitions]
    (is (= :def (:kind (t/declaration (str "Emmy.Analysis.R." n)))) n))
  (doseq [n theorems
          :let [full (str "Emmy.Analysis.R." n)
                {:keys [kind statement proof]} (t/declaration full)]]
    (testing n
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? allowed-axioms (t/axioms-of full))))))

(deftest false-claims-are-rejected
  (r/install!)
  (testing "equivalence is not provable without its hypothesis"
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.R.equiv_symm")]
      (is (not (env/verifies? (k/env)
                              (t/forall [[s r/CSeq] [u r/CSeq]] (r/equiv s u))
                              proof))))))
