#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.polynomial-test
  (:require [ansatz.kernel.expr :as e]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.polynomial :as p]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]))

(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(def ^:private samples
  "Runtime polynomials covering every constructor: const, X, add, mul, neg,
  param and frac."
  (mapv #(ax/->poly-expr % 'x '[y])
        ['(+ (* 1/2 x x) (* y x) -3)
         '(- (* x (- y 5/3)))
         '7
         'x]))

(defn- instantiate
  "The body of the closed `∀ expr, …` statement at the kernel term `term`."
  [statement term]
  (e/instantiate1 (e/forall-body statement) term))

(deftest declarations-are-checked
  (is (= :installed (p/install!)))
  (let [ctx (k/base-ctx)]
    (doseq [[label kind] [[p/eval-name :def] [p/eval-q-name :def]
                          [p/cast-name :thm] [p/theorem-name :thm]]
            :let [{actual :kind :keys [statement proof]} (t/declaration ctx label)]]
      (testing label
        (is (= kind actual))
        (when (= :thm kind)
          (is (k/verifies? ctx statement proof))
          (is (every? allowed-axioms (t/axioms-of ctx label))))))))

(deftest value->term-builds-closed-polyexpr-terms
  (p/install!)
  (testing "every constructor is spelled with its kernel name"
    (let [heads (into #{}
                      (comp (mapcat #(tree-seq vector? rest %))
                            (keep (fn [v] (when (vector? v) (first v)))))
                      samples)]
      (is (= #{0 1 2 3 4 5 6} heads) "the samples reach every constructor"))
    (doseq [v samples]
      (is (not (e/has-loose-bvars? (p/value->term v))))))
  (testing "the terms are well typed: the derivative theorem applies to each"
    (let [ctx (k/base-ctx)]
      (doseq [v samples
              :let [term (p/value->term v)]]
        (is (k/verifies? ctx (p/proposition term)
                         (t/app (k/const p/theorem-name) term)))))))

(deftest eval-cast-instantiates-at-concrete-polynomials
  (p/install!)
  (let [ctx (k/base-ctx)
        {:keys [statement]} (t/declaration ctx p/cast-name)]
    (doseq [v samples
            :let [term (p/value->term v)]]
      (is (k/verifies? ctx (instantiate statement term)
                       (t/app (k/const p/cast-name) term))))))

(deftest proofs-do-not-transfer-between-polynomials
  (p/install!)
  (let [ctx (k/base-ctx)
        [a b] (map p/value->term [(ax/->poly-expr '(* x x) 'x) (ax/->poly-expr 'x 'x)])
        {:keys [statement]} (t/declaration ctx p/cast-name)]
    (testing "the derivative proof for x² does not prove the statement for x"
      (is (not (k/verifies? ctx (p/proposition b)
                            (t/app (k/const p/theorem-name) a)))))
    (testing "nor does the cast proof"
      (is (not (k/verifies? ctx (instantiate statement b)
                            (t/app (k/const p/cast-name) a)))))))
