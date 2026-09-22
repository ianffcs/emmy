#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.mathlib-test
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.mathlib :as m]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.core :as k]))

(deftest mathlib-shaped-physlib-surface
  (is (= :installed (m/install!)))
  (is (= :installed (m/install!)))
  (doseq [n ["Real" "Rat" "Norm" "Dist" "MetricSpace"
             "HasDerivAt" "Continuous" "ContinuousAt" "TendsToAt"]]
    (testing n
      (let [{:keys [kind statement proof]}
            (t/declaration (k/base-ctx) (str "Emmy.Mathlib." n))]
        (is (= :def kind))
        (is (some? (env/check-constant
                    (k/env)
                    (env/mk-def (name/from-string
                                 (str "test.Mathlib." n)) [] statement proof)))))))
  (let [{:keys [statement proof]}
        (t/declaration (k/base-ctx) "Emmy.Mathlib.MetricSpace")]
    (testing "MetricSpace is a checked structure alias, not True"
      (is (= (t/arrow t/type0 t/prop) statement))
      (is (re-find #"Emmy.Analysis.Metric.MetricSpace" (pr-str proof))))))

(deftest adapters-preserve-physlib-propositions
  (m/install!)
  (let [x (k/const "Emmy.Analysis.R.zero")
        y (k/const "Emmy.Analysis.R.one")]
    (is (= (m/dist x y)
           (m/norm (r/sub x y)))))
  (is (= (m/has-deriv-at (t/lam "x" m/Real identity) (k/const "Emmy.Analysis.R.one")
                         (k/const "Emmy.Analysis.R.zero"))
         (m/derivative-witness (t/lam "x" m/Real identity)
                               (k/const "Emmy.Analysis.R.zero")
                               (k/const "Emmy.Analysis.R.one")))))

(deftest derivative-witness-is-explicitly-deprecated
  (is (= "Use has-deriv-at; retained only for migration."
         (:deprecated (meta #'m/derivative-witness))))
  (is (nil? (resolve 'emmy.ansatz.analysis.mathlib/fderiv))))
