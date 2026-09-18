#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.simplify-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.generators :as gen]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [emmy.abstract.number]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]
            [emmy.ansatz.generators :as ag]
            [emmy.ansatz.simplify :as s]
            [emmy.expression :as x]))

(defn- simp-form [form]
  (x/expression-of (s/simplify form)))

(defn- unit-free?
  "True if `form` contains no `0 + _`, `_ * 1`, `0 * _`, `- - _` or
  arithmetic on two constants."
  [form]
  (if-not (seq? form)
    true
    (let [[op a b] form]
      (and (not (case op
                  + (or (= 0 a) (= 0 b) (and (number? a) (number? b)))
                  * (or (#{0 1} a) (#{0 1} b) (and (number? a) (number? b)))
                  - (or (number? a) (and (seq? a) (= '- (first a)) (= 2 (count a))))
                  false))
           (every? unit-free? (rest form))))))

(deftest correctness-theorem-test
  (s/install!)
  (is (k/installed? s/theorem-name))
  (doseq [lemma ["Emmy.PolyExpr.mkAdd_correct"
                 "Emmy.PolyExpr.mkMul_correct"
                 "Emmy.PolyExpr.mkNeg_correct"]]
    (is (k/installed? lemma) lemma)))

(deftest simplify-test
  (testing "units, annihilation, constant folding, double negation"
    (is (= 'x (simp-form '(+ 0 x))))
    (is (= 'x (simp-form '(* x 1))))
    (is (= 0 (simp-form '(* (+ x 3) 0))))
    (is (= 5 (simp-form '(+ 2 3))))
    (is (= -6 (simp-form '(* 2 (- 3)))))
    (is (= 'x (simp-form '(- (- x)))))
    (is (= '(* 3 (+ x x)) (simp-form '(* (+ 1 2) (+ x (* 1 x)))))))

  (testing "is local: no collection of like terms"
    (is (= '(+ x x) (simp-form '(+ x x))))))

(deftest simplify-property-test
  (checking "preserves the value (compiled eval)" 100
            [form ag/poly-form
             x (gen/choose -30 30)]
            (let [v (ax/->poly-expr form 'x)]
              (is (= (ax/eval-poly v x)
                     (ax/eval-poly (s/simp-poly v) x)))))

  (checking "is idempotent and leaves no units behind" 100
            [form ag/poly-form]
            (let [once (s/simp-poly (ax/->poly-expr form 'x))]
              (is (= once (s/simp-poly once)))
              (is (unit-free? (simp-form form))))))
