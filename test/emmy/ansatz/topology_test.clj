#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.topology-test
  (:require [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.topology :as topology]
            [emmy.ansatz.core :as k]))

(deftest kernel-topology
  (is (= :installed (topology/install!)))
  (is (= :installed (topology/install!)))
  (doseq [n ["Space" "IsOpen" "Continuous"]]
    (is (= :def (:kind (t/declaration (str "Emmy.Analysis.Topology." n))))))
  (doseq [n ["continuous_id" "continuous_comp"]]
    (let [{:keys [kind statement proof]}
          (t/declaration (str "Emmy.Analysis.Topology." n))]
      (is (= :thm kind))
      (is (env/verifies? (k/env) statement proof))
      (is (not (env/verifies? (k/env) (k/eq k/zero (k/lit 1)) proof))))))

(deftest no-axiom-installation
  (is (thrown? clojure.lang.ExceptionInfo
               (t/install-declaration! :axiom "Emmy.Analysis.False" t/prop nil)))
  (is (thrown? clojure.lang.ExceptionInfo
               (t/install-declaration! :thm "Emmy.Analysis.False" (k/const "False") nil))))
