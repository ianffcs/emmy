#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.core-test
  (:require [ansatz.kernel.expr :as e]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]))

(defn- closes?
  "True if the kernel accepts the proof map `p`, closed over `vars`."
  [ctx vars p]
  (let [{:keys [statement proof]} (k/close vars p)]
    (k/verifies? ctx statement proof)))

(deftest literals
  (testing "negative literals are spelled as the negation of a natural literal"
    (is (= (k/neg (k/lit 3)) (k/lit -3))))
  (testing "zero and one are the literals they name"
    (is (= k/zero (k/lit 0)))
    (is (= k/one (k/lit 1))))
  (testing "arbitrarily large literals are accepted"
    (is (some? (k/lit (bigint 1e40)))))
  (testing "non-integers are rejected"
    (is (thrown? AssertionError (k/lit 1/2)))))

(deftest eq-view-reads-equations
  (let [[[_ x] [_ y]] (k/fresh-vars '[x y])]
    (testing "an Int equation round-trips through eq"
      (is (= {:type k/int-type :lhs x :rhs y}
             (dissoc (k/eq-view (k/eq x y)) :level))))
    (testing "anything else is not an equation"
      (is (nil? (k/eq-view (k/add x y))))
      (is (nil? (k/eq-view t/prop))))))

(deftest proof-map-builders
  (let [ctx (k/base-ctx)
        [[_ x] [_ y] [_ z] :as vars] (k/fresh-vars '[x y z])
        comm (k/lemma-in ctx "Int.add_comm" x y)]
    (testing "an instantiated lemma carries its sides and checks"
      (is (= (k/add x y) (:lhs comm)))
      (is (= (k/add y x) (:rhs comm)))
      (is (closes? ctx vars comm)))
    (testing "reflexivity is a no-op for symm and trans"
      (let [r (k/refl x)]
        (is (k/refl? r))
        (is (identical? r (k/symm r)))
        (is (identical? comm (k/trans r comm)))
        (is (identical? comm (k/trans comm (k/refl (k/add y x)))))))
    (testing "symm and trans build checked proofs"
      (let [back (k/trans comm (k/symm comm))]
        (is (= (k/add x y) (:lhs back) (:rhs back)))
        (is (closes? ctx vars (k/symm comm)))
        (is (closes? ctx vars back))))
    (testing "congruence lifts a proof through + and *"
      (is (closes? ctx vars (k/congr-add comm (k/refl z))))
      (is (closes? ctx vars (k/congr-mul (k/refl z) comm))))
    (testing "a forged proof map is rejected by the kernel"
      (is (not (closes? ctx vars (assoc comm :rhs (k/add x x))))))
    (testing "an unknown lemma fails loudly"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown lemma"
                            (k/lemma-in ctx "Int.no_such_lemma" x))))))

(deftest close-binds-free-variables
  (let [[[_ x] :as vars] (k/fresh-vars '[x])
        {:keys [statement proof]} (k/close vars (k/refl x))]
    (is (e/forall? statement))
    (is (not (e/has-loose-bvars? statement)))
    (is (k/verifies? (k/base-ctx) statement proof))))

(deftest installed-agrees-with-lookup
  (let [ctx (k/base-ctx)]
    (is (k/installed? ctx "Int.add_comm"))
    (is (some? (k/lookup ctx "Int.add_comm")))
    (is (not (k/installed? ctx "Int.no_such_constant")))
    (is (nil? (k/lookup ctx "Int.no_such_constant")))
    (is (= (k/installed? ctx "Int.add_comm") (k/installed? "Int.add_comm")))))

(deftest prove-law-accepts-surface-goals
  (let [ctx (k/base-ctx)]
    (testing "a surface statement is elaborated under typed binders and proved"
      (let [[statement proof] (k/prove-law ctx '[n :- Nat] '(= Nat n n) '[(rfl)])]
        (is (e/forall? statement))
        (is (k/verifies? ctx statement proof))))
    (testing "a false surface statement fails loudly"
      (is (thrown? Exception
                   (k/prove-law ctx '[n :- Nat] '(= Nat n (+ n 1)) '[(rfl)]))))))

(deftest declare-theorem-is-pure-and-idempotent
  (let [ctx (k/base-ctx)
        label "Test.Core.nat_refl"
        declared (t/declare-theorem ctx label '[n :- Nat] '(= Nat n n) '[(rfl)])]
    (testing "the theorem lands in the returned context only"
      (is (k/installed? declared label))
      (is (not (k/installed? ctx label)))
      (is (not (k/installed? label))))
    (testing "its stored statement and proof check"
      (let [{:keys [kind statement proof]} (t/declaration declared label)]
        (is (= :thm kind))
        (is (k/verifies? declared statement proof))))
    (testing "re-declaring an installed name leaves the context alone"
      (is (identical? declared
                      (t/declare-theorem declared label '[n :- Nat] '(= Nat n n) '[(rfl)]))))
    (testing "an unprovable theorem is not declared"
      (is (thrown? Exception
                   (t/declare-theorem ctx "Test.Core.bad" '[n :- Nat]
                                      '(= Nat n (+ n 1)) '[(rfl)]))))))
