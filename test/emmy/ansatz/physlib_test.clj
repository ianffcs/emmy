#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.physlib-test
  (:require [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]
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

(deftest real-derivative-proofs
  (doseq [expr ['(/ (* x x) 2) '(* 1/3 (expt x 3)) '(* -2/7 x y) 4/9]]
    (is (physlib/derivative-proof? (physlib/derivative-proof expr 'x))))
  (let [p (physlib/derivative-proof '(* 1/2 x x y) 'x)]
    (is (= ['y] (:params p)))
    (is (not (physlib/derivative-proof? (assoc p :proof nil))))
    (is (not (physlib/derivative-proof? (assoc p :statement (k/eq k/zero (k/lit 1))))))
    (is (not (physlib/derivative-proof? (assoc p :expression '(* x x x)))))
    (is (not (physlib/derivative-proof? (assoc p :params ['z]))))))

(deftest euler-lagrange-facts-are-checked-theorems
  (is (= [:free-particle-force :free-particle-momentum :momentum-derivative :uniform-motion]
         (vec (keys (physlib/lagrange-facts)))))
  (doseq [fact (keys (physlib/lagrange-facts))
          :let [{:keys [theorem statement proof]} (physlib/lagrange-proof fact)]]
    (testing (str fact)
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? #{"propext" "Quot.sound" "Classical.choice"} (t/axioms-of theorem)))))
  (testing "an unknown fact is refused rather than guessed at"
    (is (thrown? clojure.lang.ExceptionInfo (physlib/lagrange-proof :gravity)))))
