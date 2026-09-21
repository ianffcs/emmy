#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.real-topology-test
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.real-topology :as rt]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.analysis.topology :as top]
            [emmy.ansatz.core :as k]))

(def ^:private prefix "Emmy.Analysis.RealTopology.")
(def ^:private allowed-axioms #{"propext" "Quot.sound" "Classical.choice"})

(deftest epsilon-ball-topology
  (is (= :installed (rt/install!)))
  (is (= :installed (rt/install!)))
  (doseq [n ["Ball" "IsOpen" "space"]
          :let [{:keys [kind statement proof]} (t/declaration (str prefix n))]]
    (testing n
      (is (= :def kind))
      (is (some? (env/check-constant
                  (k/env) (env/mk-def (name/from-string (str "test.RealTopology." n))
                                      [] statement proof))))
      (is (every? allowed-axioms (t/axioms-of (str prefix n))))))
  (doseq [n ["isOpen_empty" "isOpen_univ" "isOpen_inter" "isOpen_sUnion"
             "mem_ball_self" "isOpen_ball" "continuous_iff"]
          :let [{:keys [kind statement proof]} (t/declaration (str prefix n))]]
    (testing n
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof)))
      (is (every? allowed-axioms (t/axioms-of (str prefix n)))))))

(deftest bridge-matches-the-public-proposition
  (rt/install!)
  (let [FnR (t/arrow r/R r/R)
        analytic #(t/app (k/const "Emmy.Analysis.R.Continuous") %)
        topological #(top/continuous r/R r/R rt/real-space rt/real-space %)
        {:keys [proof]} (t/declaration (str prefix "continuous_iff"))]
    (is (env/verifies? (k/env)
          (t/forall [[f FnR]] (t/iff (analytic f) (topological f))) proof))
    (testing "the bridge does not claim that every function is continuous"
      (is (not (env/verifies? (k/env)
                 (t/forall [[f FnR]] (topological f)) proof))))))
