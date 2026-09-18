#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.rational-test
  (:require [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.rational :as rational]
            [emmy.ansatz.core :as k]))

(deftest exact-representatives
  (is (= [-1N 2N] (rational/representative 2 -4)))
  (is (= [0N 1N] (rational/representative 0 -4)))
  (is (= [5N 6N] (rational/add [1 2] [1 3])))
  (is (= [-1N 2N] (rational/multiply [3 4] [-2 3])))
  (is (= [1N 2N] (rational/negate [-2 4])))
  (is (rational/equivalent? [2 4] [1 2]))
  (is (not (rational/equivalent? [2 4] [2 3])))
  (is (= [9223372036854775808N 1N]
         (rational/add [Long/MAX_VALUE 1] [1 1])))
  (doseq [[n d] [[1 0] [0.5 1] [1 2.0]]]
    (is (thrown? clojure.lang.ExceptionInfo (rational/representative n d))))
  (is (thrown? clojure.lang.ExceptionInfo (rational/add [1 -2] [1 2]))))

(deftest representative-laws-are-kernel-proofs
  (let [laws (rational/arithmetic-laws)]
    (is (= #{:add-comm :add-assoc :mul-comm :mul-assoc :distrib
             :add-zero :mul-one :add-neg} (set (keys laws))))
    (doseq [[_ {:keys [statement proof]}] laws]
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof))))))

(def ^:private kernel-theorems
  ["den_pos" "int_mul_right_cancel" "equiv_refl" "equiv_symm" "equiv_trans"
   "add_congr" "mul_congr" "neg_congr"])

(deftest kernel-layer
  (is (= :installed (rational/install!)))
  (is (= :installed (rational/install!)) "idempotent")
  (testing "definitions"
    (doseq [n ["Rep" "num" "den" "Equiv" "add" "mul" "neg"]]
      (is (= :def (:kind (t/declaration (str "Emmy.Analysis.Rational." n)))) n)))
  (testing "every theorem re-checks against its full statement"
    (doseq [n kernel-theorems]
      (let [{:keys [kind statement proof]} (t/declaration (str "Emmy.Analysis.Rational." n))]
        (is (= :thm kind) n)
        (is (env/verifies? (k/env) statement proof) n)
        (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)) n))))
  (testing "a proof can't be reused for a stronger, false statement"
    ;; equiv_symm's proof does not prove `∀ a b, Equiv a b` (no hypothesis).
    (let [{:keys [proof]} (t/declaration "Emmy.Analysis.Rational.equiv_symm")
          rep (k/const "Emmy.Analysis.Rational.Rep")
          false-statement (t/forall [[a rep] [b rep]]
                            (t/app (k/const "Emmy.Analysis.Rational.Equiv") a b))]
      (is (not (env/verifies? (k/env) false-statement proof)))
      (is (thrown? Exception
                   (t/install-declaration! :thm "Emmy.Analysis.Rational.bogus"
                                           false-statement proof))))))
