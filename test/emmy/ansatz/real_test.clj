#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.real-test
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.real :as real]
            [emmy.ansatz.core :as k]))

(deftest cauchy-carrier
  (is (= :installed (real/install!)))
  (is (= :installed (real/install!)))
  (doseq [n ["RationalRep" "Within" "Cauchy" "CauchySequence"
             "constantSequence" "rationalSequence"
             "Equivalent" "Carrier" "ofCauchy" "ofRationalRep"]]
    (let [{:keys [kind statement proof]}
          (t/declaration (str "Emmy.Analysis.RealConstruction." n))]
      (is (= :def kind))
      (is (some? (env/check-constant
                  (k/env)
                  (env/mk-def (name/from-string (str "test.Real." n)) [] statement proof))))))
  (doseq [n ["sound" "within_self" "constant_cauchy"]]
    (let [{:keys [kind statement proof]}
          (t/declaration (str "Emmy.Analysis.RealConstruction." n))]
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof))))))
