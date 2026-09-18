#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.expression-test
  (:require [clojure.test :refer [deftest is testing]]
            [clojure.test.check.generators :as gen]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [emmy.abstract.number]
            [emmy.ansatz.expression :as ax]
            [emmy.ansatz.generators :as ag]
            [emmy.generic :as g]))

(deftest ->ir-test
  (testing "arithmetic"
    (is (= [:add [:add [:var 'x] [:lit 1]] [:var 'y]] (ax/->ir '(+ x 1 y))))
    (is (= [:sub [:var 'x] [:lit 2]] (ax/->ir '(- x 2))))
    (is (= [:neg [:var 'x]] (ax/->ir '(- x))))
    (is (= [:mul [:var 'x] [:lit 1/2]] (ax/->ir '(/ x 2)))))

  (testing "powers unfold into products"
    (is (= [:mul [:mul [:var 'x] [:var 'x]] [:var 'x]] (ax/->ir '(expt x 3))))
    (is (= [:mul [:var 'x] [:var 'x]] (ax/->ir '(square x))))
    (is (= [:lit 1] (ax/->ir '(expt x 0)))))

  (testing "Emmy symbolic values"
    (is (= [:add [:var 'x] [:lit 1]] (ax/->ir (g/+ 'x 1)))))

  (testing "unsupported input"
    (doseq [form ['(sin x) '(expt x -1) '(expt x y) '(/ 1 x) 1.5]]
      (is (= ::ax/unsupported
             (try (ax/->ir form) nil
                  (catch clojure.lang.ExceptionInfo e (:type (ex-data e)))))
          (pr-str form)))))

(deftest poly-expr-test
  (ax/install!)
  (testing "runtime representation"
    (is (= [3 [1] [2 [0 5] [1]]] (ax/->poly-expr '(* x (+ 5 x)) 'x))))

  (testing "other symbols become numbered parameters"
    (is (= [3 [1] [2 [0 5] [5 0]]] (ax/->poly-expr '(* x (+ 5 y)) 'x)))
    (is (= [3 [5 0] [2 [0 5] [1]]] (ax/->poly-expr '(* x (+ 5 y)) 'y)))
    (is (= 11 (ax/eval-poly (ax/->poly-expr '(+ x (* y z)) 'x) 1 [2 5]))))

  (testing "rational coefficients become frac nodes"
    (is (= [3 [1] [6 1 1]] (ax/->poly-expr '(/ x 2) 'x))))

  (checking "IR ⇄ PolyExpr round trip preserves values" 100
            [form ag/poly-form
             x (gen/choose -50 50)]
            (let [ir (ax/->ir form)
                  v  (ax/ir->value ir 'x)]
              (is (= (ax/evaluate ir {'x x})
                     (ax/evaluate (ax/value->ir v 'x) {'x x})))))

  (checking "the compiled, verified eval agrees with the IR" 100
            [form ag/poly-form
             x (gen/choose -50 50)]
            (is (= (ax/evaluate (ax/->ir form) {'x x})
                   (ax/eval-poly (ax/->poly-expr form 'x) x)))))

(deftest multivariate-eval-test
  (ax/install!)
  (checking "the compiled eval agrees with the IR with parameters" 100
            [form (ag/poly-form-over '[x y z])
             vals (gen/vector (gen/choose -20 20) 3)]
            (let [ir (ax/->ir form)
                  params (ax/params-of ir 'x)
                  env (zipmap '[x y z] vals)]
              (is (= (ax/evaluate ir env)
                     (ax/eval-poly (ax/ir->value ir 'x params) (env 'x) (mapv env params)))))))

(deftest rational-values-test
  (ax/install!)
  (testing "fractions are frac nodes, p/(q+1)"
    (is (= [6 -3 3] (ax/->poly-expr -3/4 'x)))
    (is (= -3/4 (ax/eval-poly (ax/->poly-expr -3/4 'x) 0))))
  (testing "evaluation is exact"
    (is (= 21/2 (ax/eval-poly (ax/->poly-expr '(+ (* 1/2 x x) (* 3 y)) 'x) 3 [2]))))
  (checking "the compiled num/den agrees with the IR on rational forms" 100
            [form (ag/poly-form-over '[x y z])
             vals (gen/vector (gen/choose -20 20) 3)]
            (let [ir (ax/->ir form)
                  params (ax/params-of ir 'x)
                  env (zipmap '[x y z] vals)]
              (is (= (ax/evaluate ir env)
                     (ax/eval-poly (ax/ir->value ir 'x params) (env 'x) (mapv env params)))))))
