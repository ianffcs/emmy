#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.codegen-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.generators :as gen]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [emmy.ansatz.codegen :as codegen]
            [emmy.ansatz.expression :as ax]
            [emmy.ansatz.generators :as ag]
            [emmy.expression :as x]
            ;; generic arithmetic on Clojure numbers, for ag/->fn-of
            [emmy.numbers]))

(deftest ->form-renders-every-constructor
  (testing "const, X and param"
    (is (= 5 (codegen/->form [0 5] 'x)))
    (is (= 'x (codegen/->form [1] 'x)))
    (is (= 'b (codegen/->form [5 1] 'x '[a b]))))
  (testing "frac p q is the ratio p/(q+1)"
    (is (= 1/2 (codegen/->form [6 1 1] 'x)))
    (is (= -3/4 (codegen/->form [6 -3 3] 'x)))
    (is (= 7 (codegen/->form [6 7 0] 'x))))
  (testing "add, mul and neg stay binary and structural"
    (is (= '(+ (* x a) (- 1/2))
           (codegen/->form [2 [3 [1] [5 0]] [4 [6 1 1]]] 'x '[a])))))

(deftest ->emmy-wraps-only-compound-forms
  (is (= 5 (codegen/->emmy [0 5] 'x)))
  (is (= 'y (codegen/->emmy [1] 'y)))
  (is (= 'a (codegen/->emmy [5 0] 'x '[a])))
  (let [e (codegen/->emmy [2 [1] [5 0]] 'x '[a])]
    (is (x/literal? e))
    (is (= '(+ x a) (x/expression-of e)))))

(deftest round-trip-preserves-values
  (let [syms '[x y]
        point (gen/tuple (gen/choose -9 9) (gen/elements [-5/2 -1 0 1/3 4]))]
    (checking "Emmy form -> PolyExpr -> form evaluates the same, with parameters and rationals" 100
      [form (ag/poly-form-over syms)
       [xv yv] point]
      (let [value (ax/->poly-expr form 'x '[y])
            back (codegen/->form value 'x '[y])]
        (is (= ((ag/->fn-of syms form) xv yv)
               ((ag/->fn-of syms back) xv yv)))))))
