#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.physlib-test
  (:require [clojure.test :refer [deftest is]]
            [emmy.ansatz.expression :as expression]
            [emmy.ansatz.physlib :as physlib]
            [emmy.expression :as x]
            [emmy.generic :as g]))

(deftest rational-real-denotation
  (is (= 4.5 (physlib/approximate-value (expression/->poly-expr '(/ (* x x) 2) 'x) 3.0))))

(deftest coordinate-derivatives
  (is (= 'x (x/expression-of
             (g/simplify (physlib/time-deriv '(/ (* x x) 2) 'x)))))
  (is (= 2 (x/expression-of ((physlib/space-deriv 1 g/* 2) 2 3)))))

(deftest polynomial-report-is-not-a-certificate
  (let [certificate (physlib/polynomial-derivative-report '(/ (* x x) 2) 'x 3.0)]
    (is (false? (:certified? certificate)))
    (is (nil? (ns-resolve 'emmy.ansatz.physlib 'has-deriv-at?)))
    (is (= 4.5 (:value certificate)))
    (is (= 3.0 (:derivative-value certificate)))))
