#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.install-test
  (:require [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.install :as install]))

(deftest every-listed-namespace-has-an-installer
  (doseq [ns-sym install/ns-list]
    (testing (str ns-sym)
      (is (ifn? (install/installer ns-sym))))))

(deftest prerequisites-come-first
  (is (= ['emmy.ansatz.algebra] (install/through 'emmy.ansatz.algebra)))
  (let [order (install/through 'emmy.ansatz.analysis.lagrange)]
    (is (= 'emmy.ansatz.analysis.lagrange (peek order)))
    (is (every? (set order) '[emmy.ansatz.analysis.rational
                              emmy.ansatz.analysis.qfield
                              emmy.ansatz.analysis.reals
                              emmy.ansatz.analysis.derivative])
        "everything lagrange builds on is installed before it")
    (is (apply < (map #(.indexOf install/ns-list %) order))
        "and in ns-list order"))
  (is (thrown? clojure.lang.ExceptionInfo (install/through 'emmy.not.a.namespace)))
  (is (thrown? clojure.lang.ExceptionInfo (install/installer 'emmy.not.a.namespace))))

(deftest installing-through-a-namespace-publishes-its-declarations
  (install/install-through! 'emmy.ansatz.analysis.rational)
  (is (k/installed? "Emmy.Analysis.Rational.Equiv")))
