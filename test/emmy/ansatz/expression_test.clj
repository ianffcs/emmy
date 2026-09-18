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

  (testing "rational coefficients are not (yet) representable"
    (is (thrown? clojure.lang.ExceptionInfo (ax/->poly-expr '(/ x 2) 'x))))

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
