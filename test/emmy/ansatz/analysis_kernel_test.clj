#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis-kernel-test
  (:require [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]))

(def ^:private nat (k/const "Nat"))

(deftest implication-chain
  (is (= (t/arrow t/prop (t/arrow t/prop t/prop))
         (t/>-> t/prop t/prop t/prop)))
  (is (= '(emmy.ansatz.analysis.kernel/arrow A B)
         (macroexpand '(emmy.ansatz.analysis.kernel/>-> A B))))
  (is (= '(emmy.ansatz.analysis.kernel/arrow
           A (emmy.ansatz.analysis.kernel/arrow B C))
         (macroexpand '(emmy.ansatz.analysis.kernel/>-> A B C))))
  (is (= '(emmy.ansatz.analysis.kernel/arrow
           A (emmy.ansatz.analysis.kernel/arrow
              B (emmy.ansatz.analysis.kernel/arrow C D)))
         (macroexpand '(emmy.ansatz.analysis.kernel/>-> A B C D))))
  (is (thrown? clojure.lang.Compiler$CompilerException
                (macroexpand '(emmy.ansatz.analysis.kernel/>-> A))))
  (is (thrown? clojure.lang.Compiler$CompilerException
                (macroexpand '(emmy.ansatz.analysis.kernel/>->)))))

(deftest declarations-extend-a-context-without-touching-global-state
  (let [ctx (k/base-ctx)
        extended (t/declare-constant ctx :def "Test.Purity.N" t/type0 nat)]
    (testing "the extended context sees the constant"
      (is (k/installed? extended "Test.Purity.N"))
      (is (= :def (:kind (t/declaration extended "Test.Purity.N")))))
    (testing "neither the original context nor the global environment does"
      (is (not (k/installed? ctx "Test.Purity.N")))
      (is (not (k/installed? "Test.Purity.N")))
      (is (nil? (t/declaration "Test.Purity.N"))))))

(deftest the-kernel-checks-every-declaration
  (let [ctx (t/declare-constant (k/base-ctx) :def "Test.Checked.N" t/type0 nat)]
    (testing "a value of the wrong type is rejected"
      (is (thrown? Exception (t/declare-constant ctx :def "Test.Checked.Bad" nat nat))))
    (testing "an existing name is rejected, not silently trusted"
      (is (thrown? Exception (t/declare-constant ctx :def "Test.Checked.N" t/type0 nat))))
    (testing "only definitions and theorems, and never a missing part"
      (is (thrown? clojure.lang.ExceptionInfo
                   (t/declare-constant ctx :axiom "Test.Checked.Ax" t/type0 nat)))
      (is (thrown? clojure.lang.ExceptionInfo
                   (t/declare-constant ctx :def "Test.Checked.Nil" t/type0 nil))))))

(deftest a-value-may-depend-on-the-context
  (let [seen (atom nil)
        ctx (-> (k/base-ctx)
                (t/declare-constant :def "Test.Lazy.A" t/type0 nat)
                (t/declare-constant :def "Test.Lazy.B" t/type0
                                    (fn [c] (reset! seen (k/installed? c "Test.Lazy.A")) nat)))]
    (is (true? @seen) "the function receives the context holding earlier declarations")
    (is (k/installed? ctx "Test.Lazy.B"))))

(deftest declarers-are-idempotent
  (let [decl (t/declarer "Test.Declarer.")
        define (t/with-kind decl :def)
        ctx (-> (k/base-ctx)
                (define "N" t/type0 nat)
                (define "N" t/type0 nat))]
    (is (k/installed? ctx "Test.Declarer.N") "the prefix is applied")
    (is (= :def (:kind (t/declaration ctx "Test.Declarer.N"))))
    (testing "an already-declared constant is left exactly as it was"
      (is (identical? ctx (define ctx "N" t/type0 nat))))))

(deftest commit-is-all-or-nothing
  (testing "a failing installer leaves the global environment unchanged"
    (is (thrown? Exception
                 (k/commit! (fn [ctx]
                              (-> ctx
                                  (t/declare-constant :def "Test.Atomic.Good" t/type0 nat)
                                  (t/declare-constant :def "Test.Atomic.Bad" nat nat))))))
    (is (not (k/installed? "Test.Atomic.Good"))))
  (testing "a successful installer is published and returned"
    (let [ctx (k/commit! #(t/declare-constant % :def "Test.Atomic.Kept" t/type0 nat))]
      (is (k/installed? ctx "Test.Atomic.Kept"))
      (is (k/installed? "Test.Atomic.Kept")))))

(deftest axiom-audit-follows-the-context
  (let [allowed #{"propext" "Quot.sound" "Classical.choice"}]
    (is (= allowed (t/axioms-of (k/base-ctx) "Classical.em")))
    (is (= #{} (t/axioms-of (k/base-ctx) "Nat.add_comm")))
    (is (= #{} (t/axioms-of (k/base-ctx) "No.Such.Constant")) "unknown names have no axioms")))
