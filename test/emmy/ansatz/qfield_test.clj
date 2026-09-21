#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.qfield-test
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as level]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.qfield :as q]
            [emmy.ansatz.core :as k]))

(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(def ^:private theorems
  ["add_comm" "add_assoc" "zero_add" "add_left_neg" "mul_comm" "mul_assoc" "one_mul"
   "left_distrib" "lt_congr_rep" "le_congr_rep" "lt_irrefl" "le_refl" "le_of_lt" "lt_trans"
   "le_trans" "lt_of_lt_of_le" "lt_of_le_of_lt" "le_antisymm" "lt_trichotomy"
   "add_lt_add_left" "add_le_add_left" "mul_pos" "mul_nonneg" "abs_congr_rep" "abs_nonneg"
   "abs_mul" "abs_triangle" "archimedean" "half_add_half" "half_pos" "inv_congr_rep"
   "mul_inv_cancel" "ne_of_lt" "zero_lt_one" "zero_ne_one" "inv_pos"
   ;; metric lemmas
   "sub_self" "neg_sub" "sub_add_sub" "add_sub_cancel" "abs_zero" "abs_neg" "abs_sub_comm"
   "dist_triangle" "add_lt_add" "sub_add_add" "neg_sub_neg" "dist_add_le" "dist_neg"
   "half_pos_of_pos"
   ;; multiplication and order
   "add_zero" "mul_lt_mul_of_pos_left" "mul_le_mul_of_nonneg_left" "le_add_of_nonneg_right"
   "le_add_of_nonneg_left" "lt_add_of_pos_right" "lt_add_of_pos_left" "abs_le_add_dist"
   "mul_sub_mul" "dist_mul_le" "mul_lt_of_lt_of_lt" "mul_inv_mul"
   ;; order extras
   "le_abs" "add_lt_add_right" "sub_half" "add_pos" "add_right_neg" "sub_add_cancel"
   "add_sub_add_left" "half_lt_self" "lt_of_sub_pos" "sub_pos_of_lt" "close_lower"
   "sub_zero" "add_sub_cancel_right" "lt_of_not_le" "half_lt_abs" "abs_of_pos"
   "neg_pos_of_neg" "sub_lt_of_dist_lt" "neg_lt_neg" "sub_lt_sub_left"
   ;; inverse algebra
   "sub_mul" "left_distrib_sub" "mul_left_comm" "mul_one" "mul_congr_fst" "mul_congr_snd"
   "sub_congr_fst" "sub_congr_snd" "abs_congr" "inv_mul_cancel" "inv_eq_of_mul_eq_one"
   "inv_zero" "abs_one" "abs_of_neg" "abs_pos_of_ne_zero" "abs_inv" "inv_lt_inv_of_lt"
   "inv_sub_inv" "inv_mul_mul" "ne_zero_of_lt_abs" "abs_inv_lt" "dist_inv_lt"
   "quarter_gap_left" "quarter_gap_right" "lt_add_of_abs_sub_lt"
   ;; the rational null sequence and le arithmetic
   "ofInt_le" "ofNat_le" "ofNat_succ_pos" "archimedean_nat" "inv_inv" "inv_le_inv_of_le"
   "small_pos" "small_mono" "small_lt" "add_sub_cancel_left" "add_le_add_right"
   "sub_nonneg_of_le" "le_of_sub_nonneg" "neg_le_neg" "sub_le_sub_left" "abs_le_of_bounds"
   "abs_sub_abs_le" "triangle_gap" "lt_double_sub" "quarter_add_quarter"
   "quarter_half_quarter"
   ;; gap lemmas for limits
   "mul_sub_decomp" "mul_expand" "sub_swap" "lt_sub_of_add_lt" "half_lt_one"
   "half_lt_abs_add_one" "abs_gap" "mul_gap"])

(def ^:private definitions ["Q" "zero" "one" "add" "mul" "neg" "sub" "lt" "le" "abs"
                            "inv" "ofInt" "ofNat" "half" "small"])

(deftest ordered-field-theorems
  (is (= :installed (q/install!)))
  (is (= :installed (q/install!)) "idempotent")
  (doseq [n definitions]
    (is (= :def (:kind (t/declaration (str "Emmy.Analysis.Q." n)))) n))
  (doseq [n theorems
          :let [full (str "Emmy.Analysis.Q." n)
                {:keys [kind statement proof]} (t/declaration full)]]
    (testing n
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? allowed-axioms (t/axioms-of full))))))

(deftest false-claims-are-rejected
  (q/install!)
  (testing "p < p can't be proved with lt_irrefl's proof"
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Q.lt_irrefl")]
      (is (not (env/verifies? (k/env) (t/forall [[p q/Q]] (q/lt p p)) proof)))))
  (testing "p · p⁻¹ = 1 needs p ≠ 0"
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Q.mul_inv_cancel")
          unconditional (t/forall [[p q/Q]] (k/eq-at q/Q (level/succ level/zero)
                                                     (q/mul p (q/inv p)) q/one))]
      (is (not (env/verifies? (k/env) unconditional proof)))
      (is (thrown? Exception
                   (t/install-declaration! :thm "Emmy.Analysis.Q.bogus" unconditional proof))))))
