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
   "add_congr" "neg_congr" "bounded_below" "bounded" "mul_cauchy" "mul_congr"
   ;; ring laws
   "equiv_of_eq" "add_comm" "add_assoc" "zero_add" "add_left_neg" "sub_self" "mul_comm"
   "mul_assoc" "one_mul" "left_distrib" "ofQ_add" "ofQ_mul" "ofQ_neg"
   ;; order
   "pos_congr" "pos_add" "sub_add_sub" "add_sub_add_left" "ofQ_sub" "positive_add"
   "not_positive_zero" "lt_irrefl" "lt_trans" "add_lt_add_left" "le_refl" "le_of_lt"
   "positive_ofQ" "ofQ_lt" "lt_ofQ"
   ;; apartness and trichotomy
   "apart_of_ne" "pos_or_neg_of_apart" "neg_sub" "sub_add_cancel" "eq_of_sub_eq_zero"
   "lt_trichotomy"
   ;; Archimedean
   "sub_zero" "archimedean" "zero_lt_ofQ"
   ;; inverse
   "apart_congr" "inv_cauchy" "inv_congr" "mul_inv_cancel"
   ;; density
   "dense"
   ;; absolute value and completeness
   "abs_cauchy" "abs_congr_seq" "abs_sub_comm" "sub_add_add" "ofQ_abs" "add_lt_add"
   "dist_triangle_lt" "abs_sub_ofQ_lt" "approx" "add_lt_add_right" "sum3_ofQ"
   "approx_cauchy" "complete"
   ;; order toolkit
   "equiv_of_eventually_eq" "lt_zero_of_Pos" "Pos_of_lt_zero" "positive_of_lt_zero"
   "lt_zero_of_positive" "ne_of_lt" "pos_apart" "abs_pos_of_ne" "abs_of_pos" "mul_pos"
   "half_pos" "half_add_half" "sub_half" "half_lt_self" "dist_add_lt" "abs_mul_lt"
   "abs_lt_add" "abs_add_one_pos" "inv_pos" "mul_congr_fst" "mul_congr_snd" "mul_inv_mul"
   "exists_pos_lt_both"
   ;; limits and continuity (M4)
   "zero_lt_one" "abs_sub_self" "dist_neg" "mul_sub_decomp" "add_sub_cancel_left"
   "abs_lt_abs_add_one" "abs_add_lt" "tendsto_const" "tendsto_id" "tendsto_add"
   "tendsto_neg" "tendsto_mul" "tendsto_unique" "continuousAt_of_tendsto"
   "continuous_const" "continuous_id"])

(def ^:private definitions
  ["Cauchy" "CSeq" "Equiv" "R" "constSeq" "ofQ" "addSeq" "negSeq" "cadd" "cneg"
   "add" "neg" "sub" "zero" "one" "mulSeq" "cmul" "mul" "Pos" "Positive" "lt" "le" "Apart" "ofInt" "invSeq" "cinv" "inv" "absSeq" "cabs" "abs" "CauchyR" "TendsTo" "half" "TendsToAt" "ContinuousAt" "Continuous"])

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
