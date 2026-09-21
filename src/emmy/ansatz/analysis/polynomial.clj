#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.polynomial
  "Real semantics and analytic derivative correctness for Emmy.PolyExpr.
  The theorem covers every real coordinate and real parameter environment."
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.derivative :as d]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.qfield :as q]
            [emmy.ansatz.analysis.rational :as rat]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.calculus :as calculus]
            [emmy.ansatz.core :as k]))

(def ^:private u (level/succ level/zero))
(def ^:private P (k/const "Emmy.PolyExpr"))
(def ^:private Nat (k/const "Nat"))
(def ^:private Rho (t/arrow Nat r/R))
(def eval-name "Emmy.PolyExpr.evalReal")
(def eval-q-name "Emmy.PolyExpr.evalQ")
(def cast-name "Emmy.PolyExpr.eval_cast")
(def theorem-name "Emmy.PolyExpr.deriv_hasDerivAt")
(defn- pc [s]
  (k/const (str "Emmy.PolyExpr." s)))

(defn- dc [s]
  (k/const (str "Emmy.Analysis.Derivative." s)))

(defn eval-real [x rho expr]
  (t/app (k/const eval-name) x rho expr))

(defn eval-q [x rho expr]
  (t/app (k/const eval-q-name) x rho expr))

(defn- function-at [rho expr]
  (t/lambda [[y r/R]] (eval-real y rho expr)))
(defn- fraction [p n]
  (r/of-q (q/mk (rat/make-rep p
    (t/app (k/const "Int.ofNat") (t/app (k/const "Nat.succ") n))
    (t/app (k/const "Int.ofNat_succ_pos") n)))))

(defn- cast-proposition [expr]
  (t/forall [[rho (t/arrow Nat q/Q)] [x q/Q]]
    (k/eq-at r/R u
      (eval-real (r/of-q x) (t/lambda [[j Nat]] (r/of-q (t/app rho j))) expr)
      (r/of-q (eval-q x rho expr)))))

(defn- install-cast! []
  (let [QRho (t/arrow Nat q/Q)
        frac-q (fn [p n]
                 (q/mk (rat/make-rep p
                   (t/app (k/const "Int.ofNat") (t/app (k/const "Nat.succ") n))
                   (t/app (k/const "Int.ofNat_succ_pos") n))))
        cast-binary
        (fn [op law a b ha hb rho x]
          (let [rrho (t/lambda [[j Nat]] (r/of-q (t/app rho j)))
                ra (eval-real (r/of-q x) rrho a) rb (eval-real (r/of-q x) rrho b)
                qa (eval-q x rho a) qb (eval-q x rho b)
                ca (r/of-q qa) cb (r/of-q qb)
                h1 (t/app (k/const "congrArg" u u) r/R r/R ra ca
                     (t/lambda [[z r/R]] (op z rb)) (t/app ha rho x))
                h2 (t/app (k/const "congrArg" u u) r/R r/R rb cb
                     (t/lambda [[z r/R]] (op ca z)) (t/app hb rho x))
                endpoint (r/of-q ((if (= law "ofQ_add") q/add q/mul) qa qb))]
            (t/app (k/const "Eq.trans" u) r/R (op ra rb) (op ca rb) endpoint h1
              (t/app (k/const "Eq.trans" u) r/R (op ca rb) (op ca cb) endpoint h2
                (t/app (k/const (str "Emmy.Analysis.R." law)) qa qb)))))]
    (when-not (k/installed? eval-q-name)
      (t/install-declaration! :def eval-q-name (t/arrow q/Q (t/arrow QRho (t/arrow P q/Q)))
        (t/lambda [[x q/Q] [rho QRho] [expr P]]
          (t/app (k/const "Emmy.PolyExpr.rec" u)
            (t/lam "e" P (fn [_] q/Q))
            (t/lambda [[a k/int-type]] (q/of-int a)) x
            (t/lambda [[_a P] [_b P] [va q/Q] [vb q/Q]] (q/add va vb))
            (t/lambda [[_a P] [_b P] [va q/Q] [vb q/Q]] (q/mul va vb))
            (t/lambda [[_a P] [va q/Q]] (q/neg va))
            (t/lambda [[j Nat]] (t/app rho j))
            (t/lambda [[p k/int-type] [n Nat]] (frac-q p n)) expr))))
    (when-not (k/installed? cast-name)
      (t/install-declaration! :thm cast-name (t/forall [[expr P]] (cast-proposition expr))
        (t/app (k/const "Emmy.PolyExpr.rec" level/zero)
          (t/lambda [[expr P]] (cast-proposition expr))
          (t/lambda [[a k/int-type] [_rho QRho] [_x q/Q]]
            (:term (k/refl (r/of-q (q/of-int a)) r/R u)))
          (t/lambda [[_rho QRho] [x q/Q]] (:term (k/refl (r/of-q x) r/R u)))
          (t/lambda [[a P] [b P] [ha (cast-proposition a)] [hb (cast-proposition b)] [rho QRho] [x q/Q]]
            (cast-binary r/add "ofQ_add" a b ha hb rho x))
          (t/lambda [[a P] [b P] [ha (cast-proposition a)] [hb (cast-proposition b)] [rho QRho] [x q/Q]]
            (cast-binary r/mul "ofQ_mul" a b ha hb rho x))
          (t/lambda [[a P] [ha (cast-proposition a)] [rho QRho] [x q/Q]]
            (let [ra (eval-real (r/of-q x) (t/lambda [[j Nat]] (r/of-q (t/app rho j))) a)
                  qa (eval-q x rho a) ca (r/of-q qa)
                  h (t/app (k/const "congrArg" u u) r/R r/R ra ca
                      (k/const "Emmy.Analysis.R.neg") (t/app ha rho x))]
              (t/app (k/const "Eq.trans" u) r/R (r/neg ra) (r/neg ca) (r/of-q (q/neg qa)) h
                (t/app (k/const "Emmy.Analysis.R.ofQ_neg") qa))))
          (t/lambda [[j Nat] [rho QRho] [_x q/Q]] (:term (k/refl (r/of-q (t/app rho j)) r/R u)))
          (t/lambda [[p k/int-type] [n Nat] [_rho QRho] [_x q/Q]]
            (:term (k/refl (r/of-q (frac-q p n)) r/R u))))))))

(defn proposition
  "The closed analytic derivative proposition for a closed PolyExpr term."
  [expr]
  (t/forall [[rho Rho] [x r/R]]
    (d/has-deriv-at (function-at rho expr)
      (eval-real x rho (t/app (pc "deriv") expr)) x)))

(defn value->term
  "Converts a runtime polynomial to its exact kernel constructor term."
  [[tag a b]]
  (case tag
    0 (t/app (pc "const") (k/lit a))
    1 (pc "X")
    2 (t/app (pc "add") (value->term a) (value->term b))
    3 (t/app (pc "mul") (value->term a) (value->term b))
    4 (t/app (pc "neg") (value->term a))
    5 (t/app (pc "param") (e/lit-nat a))
    6 (t/app (pc "frac") (k/lit a) (e/lit-nat b))))

(defn install!
  "Installs evalReal and its structural HasDerivAt theorem. Real evaluation is
  a non-executable kernel definition, not a conversion to floating point."
  []
  (locking k/install-lock
    (d/install!)
    (calculus/install!)
    (when-not (k/installed? eval-name)
      (t/install-declaration! :def eval-name
        (t/arrow r/R (t/arrow Rho (t/arrow P r/R)))
        (t/lambda [[x r/R] [rho Rho] [expr P]]
          (t/app (k/const "Emmy.PolyExpr.rec" u)
            (t/lam "e" P (fn [_] r/R))
            (t/lambda [[a k/int-type]] (r/of-q (q/of-int a))) x
            (t/lambda [[_a P] [_b P] [va r/R] [vb r/R]] (r/add va vb))
            (t/lambda [[_a P] [_b P] [va r/R] [vb r/R]] (r/mul va vb))
            (t/lambda [[_a P] [va r/R]] (r/neg va))
            (t/lambda [[j Nat]] (t/app rho j))
            (t/lambda [[p k/int-type] [n Nat]] (fraction p n)) expr))))
    (when-not (k/installed? theorem-name)
      (t/install-declaration! :thm theorem-name
        (t/forall [[expr P]] (proposition expr))
        (t/app (k/const "Emmy.PolyExpr.rec" level/zero)
          (t/lambda [[expr P]] (proposition expr))
          (t/lambda [[a k/int-type] [_rho Rho] [x r/R]]
            (t/app (dc "const") (r/of-q (q/of-int a)) x))
          (t/lambda [[_rho Rho] [x r/R]] (t/app (dc "id") x))
          (t/lambda [[a P] [b P] [ha (proposition a)] [hb (proposition b)] [rho Rho] [x r/R]]
            (t/app (dc "add") (function-at rho a) (function-at rho b)
              (eval-real x rho (t/app (pc "deriv") a))
              (eval-real x rho (t/app (pc "deriv") b)) x (t/app ha rho x) (t/app hb rho x)))
          (t/lambda [[a P] [b P] [ha (proposition a)] [hb (proposition b)] [rho Rho] [x r/R]]
            (t/app (dc "mul") (function-at rho a) (function-at rho b)
              (eval-real x rho (t/app (pc "deriv") a))
              (eval-real x rho (t/app (pc "deriv") b)) x (t/app ha rho x) (t/app hb rho x)))
          (t/lambda [[a P] [ha (proposition a)] [rho Rho] [x r/R]]
            (t/app (dc "neg") (function-at rho a)
              (eval-real x rho (t/app (pc "deriv") a)) x (t/app ha rho x)))
          (t/lambda [[j Nat] [rho Rho] [x r/R]] (t/app (dc "const") (t/app rho j) x))
          (t/lambda [[p k/int-type] [n Nat] [_rho Rho] [x r/R]]
            (t/app (dc "const") (fraction p n) x)))))
    (install-cast!))
  :installed)
