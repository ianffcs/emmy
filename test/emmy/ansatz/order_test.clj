#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.order-test
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.order :as o]
            [emmy.ansatz.core :as k]))

(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(def ^:private theorems
  ["lt_trans" "add_pos" "add_nonneg" "mul_nonneg" "abs_cases" "abs_nonneg" "le_abs"
   "neg_le_abs" "abs_neg" "abs_triangle" "abs_sub_comm" "abs_lt" "abs_mul"])

(deftest int-order-library
  (is (= :installed (o/install!)))
  (is (= :installed (o/install!)) "idempotent")
  (doseq [n theorems
          :let [full (str "Emmy.Analysis.Int." n)
                {:keys [kind statement proof]} (t/declaration full)]]
    (testing n
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? allowed-axioms (t/axioms-of full))))))

(deftest by-omega-test
  (o/install!)
  (let [[[_ x] [_ y] [_ h]] (k/fresh-vars '[x y h])
        xy (k/mul x y)]
    (testing "linear goals over non-linear atoms"
      ;; from 0 < x·y conclude 0 < x·y + x·y, with x·y treated as an atom
      (let [goal (o/lt k/zero (k/add xy xy))
            proof (o/by-omega goal [[(o/lt k/zero xy) h]])
            close (fn [binder body]
                    (reduce (fn [acc [nm fv type]]
                              (binder nm type (e/abstract1 acc (e/fvar-id fv)) :default))
                            body
                            [["h" h (o/lt k/zero xy)] ["y" y k/int-type] ["x" x k/int-type]]))]
        (is (env/verifies? (k/env)
                           (close e/forall' goal)
                           (close e/lam proof)))))
    (testing "false goals are rejected"
      (is (thrown? Exception (o/by-omega (o/lt xy k/zero) [[(o/lt k/zero xy) h]]))))))

(deftest audit-and-guards
  (testing "the axiom audit sees classical logic"
    (is (= allowed-axioms (t/axioms-of "Classical.em"))))
  (testing "a false theorem can't be installed with some other proof"
    (o/install!)
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Int.abs_nonneg")]
      (is (thrown? Exception
                   (t/install-declaration!
                    :thm "Emmy.Analysis.Int.bogus"
                    (t/forall [[x k/int-type]] (o/lt (o/abs x) k/zero))
                    proof))))))
