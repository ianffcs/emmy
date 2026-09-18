#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.calculus-test
  (:require [clojure.string :as str]
            [clojure.test :refer [deftest is testing]]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [emmy.ansatz.calculus :as c]
            [emmy.ansatz.codegen :as codegen]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.generators :as ag]
            [emmy.calculus.derivative :refer [D]]
            [emmy.expression :as x]
            [emmy.generic :as g]
            [emmy.simplify]
            [emmy.structure :as s]))

(defn- zero-expression? [expr]
  (= 0 (x/expression-of (g/simplify expr))))

(defn- same-derivative?
  "True if Ansatz's verified derivative of `f` equals Emmy's `D`."
  [f]
  (zero-expression? (g/- (c/derivative f) ((D f) 'x))))

(deftest correctness-theorem-test
  (c/install!)
  (testing "deriv_correct is proved and installed in the kernel environment"
    (is (k/installed? c/theorem-name))
    (is (str/includes? (c/theorem) "Emmy.PolyExpr.deriv"))))

(deftest derivative-test
  (testing "agrees with Emmy's D"
    (doseq [f [(fn [x] (g/expt (g/+ x 1) 5))
               (fn [x] (g/- (g/* 3 x x) (g/* 7 x) -2))
               (fn [x] (g/* x (g/+ 5 x)))
               (fn [x] (g/- (g/cube x)))
               (fn [_] 42)]]
      (is (same-derivative? f))))

  (testing "accepts expressions and a variable name"
    (is (zero-expression? (g/- (c/derivative (g/* 't 't 't) 't)
                               (g/* 3 't 't)))))

  (testing "returns the tree computed by Ansatz's deriv and simp"
    (is (= '(+ x x) (x/expression-of (c/derivative (fn [x] (g/* x x))))))
    (is (= 0 (c/derivative (fn [x] (g/- (g/* x 0) 7)))))
    (is (= '(+ (* (+ x x) x) (* x x))
           (x/expression-of (c/derivative (fn [x] (g/* x x x)))))))

  (testing "rejects non-polynomial input"
    (is (thrown? clojure.lang.ExceptionInfo (c/derivative g/sin)))
    (is (= '(/ 1 2N) (x/expression-of (c/derivative (fn [x] (g// x 2))))))))

(deftest derivative-property-test
  (checking "agrees with Emmy's D on random integer polynomials" 50
            [form ag/poly-form]
            (is (same-derivative? (ag/->fn form)))))

(deftest codegen-test
  (is (= '(+ (* 3 x) (- 1)) (codegen/->form [2 [3 [0 3] [1]] [4 [0 1]]] 'x)))
  (is (= 'y (codegen/->emmy [1] 'y)))
  (is (= 7 (codegen/->emmy [0 7] 'x))))

(deftest multivariate-test
  (testing "symbols other than the variable are held constant"
    (is (zero-expression? (g/- (c/derivative (g/* 'x 'y 'y) 'x) (g/* 'y 'y))))
    (is (zero-expression? (g/- (c/derivative (g/* 'x 'y 'y) 'y) (g/* 2 'x 'y))))
    (is (= 0 (c/derivative (g/* 3 'y) 'x))))

  (testing "partial derivatives of functions of several arguments"
    (let [f (fn [x y] (g/+ (g/* x x y) (g/* 5 y)))]
      (is (zero-expression? (g/- ((c/partial-derivative f 0 2) 'a 'b) (g/* 2 'a 'b))))
      (is (zero-expression? (g/- ((c/partial-derivative f 1 2) 'a 'b) (g/+ (g/* 'a 'a) 5))))
      (is (= 14 (x/expression-of ((c/partial-derivative f 1 2) 3 4))))))

  (testing "the gradient is a down of partials, like D"
    (let [f g/*
          grad ((c/gradient f 3) 'a 'b 'c)]
      (is (s/down? grad))
      (is (= 3 (count grad))))))

(deftest gradient-property-test
  (checking "agrees with Emmy's D on random polynomials in three variables" 30
            [form (ag/poly-form-over '[x y z])]
            (let [f (ag/->fn-of '[x y z] form)]
              (is (every? zero-expression?
                          (map g/- ((c/gradient f 3) 'a 'b 'c) ((D f) 'a 'b 'c)))))))
