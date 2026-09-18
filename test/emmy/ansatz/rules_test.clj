#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.rules-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.generators :as gen]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]
            [emmy.ansatz.generators :as ag]
            [emmy.ansatz.rules :as r]
            [emmy.expression :as x]))

(r/defruleset test-units
  (+ 0 ?a) => ?a
  (+ ?a 0) => ?a
  (* 1 ?a) => ?a
  (* ?a 1) => ?a
  (* 0 _) => 0
  (* _ 0) => 0
  (+ (? ?c integer?) (? ?d integer?)) => (+ ?c ?d)
  (* (? ?c integer?) (? ?d integer?)) => (* ?c ?d)
  (- (? ?c integer?)) => (- ?c)
  (- (- ?a)) => ?a)

(r/defruleset test-distribute
  (* ?a (+ ?b ?c)) => (+ (* ?a ?b) (* ?a ?c))
  (* (+ ?a ?b) ?c) => (+ (* ?a ?c) (* ?b ?c)))

(defn- simplify-form [rs form]
  (x/expression-of ((r/simplifier rs) form)))

(deftest theorems-test
  (testing "every rule, step and simp is proved in the kernel"
    (is (= 12 (count (:theorems test-units))))
    (doseq [t (:theorems test-units)]
      (is (k/installed? t) t))))

(deftest rewriting-test
  (is (= 'x (simplify-form test-units '(+ 0 x))))
  (is (= '(* 2 x) (simplify-form test-units '(* 2 (- (- (+ x 0)))))))
  (is (= -6 (simplify-form test-units '(* 2 (- 3)))))
  (is (= '(* x 3) (simplify-form test-units '(* x (+ 3 (* 0 x))))))
  (testing "rules fire bottom-up and to a fixpoint"
    (is (= '(+ (+ (* x x) (* 2 x)) (+ (* x 1) (* 2 1)))
           (simplify-form test-distribute '(* (+ x 2) (+ x 1)))))))

(deftest rejection-test
  (testing "unsound rules are rejected, naming the rule"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"rule 1 is not sound"
                          (r/ruleset* 'test-bad '[(+ 0 ?a) => ?a
                                                  (+ ?a ?b) => (* ?a ?b)]))))
  (testing "unsupported patterns"
    (doseq [rules ['[(+ ?a ?a) => (* 2 ?a)]
                   '[(+ ??a) => 0]
                   '[(sin ?a) => ?a]
                   '[(+ ?a 0) => ?b]]]
      (is (= ::r/unsupported
             (try (r/ruleset* 'test-unsupported rules) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          (pr-str rules))))
  (testing "a name can't be redefined with different rules"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"already defined"
                          (r/ruleset* 'test-units '[(+ 0 ?a) => ?a])))))

(deftest value-preservation-test
  (checking "rewriting preserves the value" 100
            [form ag/poly-form
             x (gen/choose -30 30)]
            (let [v (ax/->poly-expr form 'x)]
              (is (= (ax/eval-poly v x)
                     (ax/eval-poly (r/rewrite test-units v) x)
                     (ax/eval-poly (r/rewrite test-distribute v) x))))))
