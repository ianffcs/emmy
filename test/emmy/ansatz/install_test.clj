#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.install-test
  (:require [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.install :as install]))

(def ^:private nat (k/const "Nat"))

(defn- fixture
  "A throwaway installing namespace whose `install` is `steps`, plus a fresh
  constant-name prefix for the declarations it makes."
  [steps]
  (let [ns-sym (gensym "emmy.ansatz.install-test.fixture")]
    (intern (create-ns ns-sym) 'install steps)
    ns-sym))

(defn- declare-nat [label]
  (fn [ctx] (t/declare-constant ctx :def label t/type0 nat)))

(deftest every-listed-namespace-has-an-installer
  (doseq [ns-sym install/ns-list]
    (testing (str ns-sym)
      (let [steps (install/installer ns-sym)]
        (is (seq steps))
        (is (every? #{:pure :io} (map :kind steps)))))))

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
  (testing "the compiled-function namespaces don't pull in the real analysis"
    (is (not-any? (set (install/through 'emmy.ansatz.simplify))
                  '[emmy.ansatz.analysis.qfield emmy.ansatz.analysis.reals])))
  (is (thrown? clojure.lang.ExceptionInfo (install/through 'emmy.not.a.namespace)))
  (is (thrown? clojure.lang.ExceptionInfo (install/installer 'emmy.not.a.namespace))))

(deftest install!-runs-steps-once-and-marks-the-namespace
  (let [runs (atom [])
        a (str (gensym "Test.Install.A"))
        b (str (gensym "Test.Install.B"))
        ns-sym (fixture [(install/pure (comp (declare-nat a) #(do (swap! runs conj :pure) %)))
                         (install/io #(swap! runs conj :io))
                         (install/pure (declare-nat b))])]
    (install/install! ns-sym)
    (testing "every step ran, in order, and the pure steps were committed"
      (is (= [:pure :io] @runs))
      (is (k/installed? (k/base-ctx) a))
      (is (k/installed? (k/base-ctx) b))
      (is (install/installed-ns? (k/base-ctx) ns-sym)))
    (testing "installing again is a marker lookup"
      (install/install! ns-sym)
      (is (= [:pure :io] @runs)))))

(deftest a-failing-step-leaves-no-marker
  (let [c (str (gensym "Test.Install.C"))
        ns-sym (fixture [(install/pure (comp (fn [_] (throw (ex-info "boom" {})))
                                             (declare-nat c)))])]
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"boom" (install/install! ns-sym)))
    (is (not (k/installed? (k/base-ctx) c)))
    (is (not (install/installed-ns? (k/base-ctx) ns-sym)))))

(deftest pure-install-refuses-io-until-installed
  (let [d (str (gensym "Test.Install.D"))
        pure-ns (fixture [(install/pure (declare-nat d))])
        io-ns (fixture [(install/io (fn [] nil))])]
    (testing "a pure namespace extends the context only"
      (let [ctx (install/install (k/base-ctx) [pure-ns])]
        (is (k/installed? ctx d))
        (is (install/installed-ns? ctx pure-ns))
        (is (not (k/installed? (k/base-ctx) d)))))
    (testing "a namespace needing IO can't be installed purely"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"needs IO"
                            (install/install (k/base-ctx) [io-ns]))))
    (testing "once installed globally, the pure path skips it"
      (install/install! io-ns)
      (let [ctx (k/base-ctx)]
        (is (identical? ctx (install/install ctx [io-ns])))))))

(deftest installing-through-a-namespace-publishes-its-declarations
  (install/install-through! 'emmy.ansatz.analysis.rational)
  (is (k/installed? "Emmy.Analysis.Rational.Equiv")))

(deftest installing-everything-through-the-registry
  (install/install-all!)
  (let [ctx (k/base-ctx)]
    (testing "every listed namespace is marked"
      (is (every? #(install/installed-ns? ctx %) install/ns-list)))
    (testing "ring identities that pure installers declare for themselves"
      (is (k/installed? ctx "Emmy.Analysis.R.DerivativeRing.cancel_reorder"))
      (is (k/installed? ctx "Emmy.Analysis.R.LagrangeRing.mul_zero")))
    (testing "namespaces whose install still defines compiled functions"
      (is (k/installed? ctx "Emmy.PolyExpr.deriv_correct"))
      (is (k/installed? ctx "Emmy.PolyExpr.simp_correct")))))
