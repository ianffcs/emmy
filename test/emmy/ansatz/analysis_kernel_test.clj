#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis-kernel-test
  (:require [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]))

(deftest continuation-bindings
  (testing "sequential scope, multiple values, and single evaluation"
    (let [calls (atom [])
          eliminate (fn [v next-proof]
                      (swap! calls conj v)
                      (next-proof v (inc v)))
          result (t/with-cont [[a ha] (eliminate 2)
                               [b hb] (eliminate (+ a ha))]
                   [a ha b hb])]
      (is (= [2 3 5 6] result))
      (is (= [2 5] @calls))))
  (testing "empty chain and lexical shadowing"
    (is (= :result (t/with-cont [] :result)))
    (let [x 10
          call (fn [v next-proof] (next-proof (inc v)))]
      (is (= 12 (t/with-cont [[x] (call x) [x] (call x)] x)))))
  (testing "malformed bindings fail during expansion"
    (doseq [form ['(emmy.ansatz.analysis.kernel/with-cont [x] x)
                 '(emmy.ansatz.analysis.kernel/with-cont [x (f)] x)
                 '(emmy.ansatz.analysis.kernel/with-cont [[x] 42] x)]]
      (is (thrown? Exception (macroexpand form))))))
