#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.metric-test
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.metric :as metric]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.core :as k]))

(def ^:private prefix "Emmy.Analysis.Metric.")
(def ^:private u1 (level/succ level/zero))
(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(deftest metric-space-vocabulary
  (is (= :installed (metric/install!)))
  (is (= :installed (metric/install!)) "idempotent")
  (doseq [n ["Distance" "MetricSpace" "Ball" "IsOpen" "realDistance" "realInstance" "space"]
          :let [{:keys [kind statement proof]} (t/declaration (str prefix n))]]
    (testing n
      (is (= :def kind))
      (is (some? (env/check-constant
                  (k/env) (env/mk-def (name/from-string (str "test.Metric." n))
                                      [] statement proof))))))
  (let [{:keys [kind statement proof]} (t/declaration (str prefix "realMetricLaws"))]
    (testing "realMetricLaws"
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? allowed-axioms (t/axioms-of (str prefix "realMetricLaws")))))))

(deftest real-distance-matches-absolute-difference
  (metric/install!)
  (is (= (metric/real-distance r/zero r/one)
         (r/abs (r/sub r/zero r/one)))))

(deftest metric-space-bridges-are-checked-proofs
  (metric/install!)
  (let [M metric/real-metric-space
        dist #(metric/distance metric/real-metric-distance %1 %2)]
    (testing "dist-self"
      (is (env/verifies? (k/env)
                          (t/forall [[x r/R]] (k/eq-at r/R u1 (dist x x) r/zero))
                          (metric/dist-self r/R M))))
    (testing "dist-comm"
      (is (env/verifies? (k/env)
                          (t/forall [[x r/R] [y r/R]] (k/eq-at r/R u1 (dist x y) (dist y x)))
                          (metric/dist-comm r/R M))))
    (testing "dist-triangle rejects a false bound"
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) (metric/dist-triangle r/R M)))))))
