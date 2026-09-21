#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.real
  "Cauchy-sequence construction: definitions of the prospective real carrier.

  A rational representative (n,d) denotes n/(d+1), with n : Int and d : Nat.
  Distances are expressed by exact integer inequalities, not floating point.
  Cauchy sequences carry their Cauchy proof; the carrier identifies sequences
  whose difference tends to zero. All declarations are kernel checked.

  IMPORTANT: quotient soundness is not a completeness or field theorem.
  Equivalence, lifted arithmetic, order, completeness and the connection to
  topology remain to be proved. This namespace does not expose HasDerivAt."
  (:refer-clojure :exclude [num])
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [emmy.ansatz.algebra :as algebra]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]))

(def ^:private u (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.RealConstruction.")
(defn- c [s] (k/const (str prefix s)))
(def ^:private nat (k/const "Nat"))
(def ^:private rep (t/app (k/const "Prod" level/zero level/zero) k/int-type nat))
(def ^:private sequence-type (t/arrow nat rep))
(defn- num [r] (t/app (k/const "Prod.fst" level/zero level/zero) k/int-type nat r))
(defn- den [r]
  (t/app (k/const "Int.ofNat")
         (t/app (k/const "Nat.succ")
                (t/app (k/const "Prod.snd" level/zero level/zero) k/int-type nat r))))
(defn- lt [a b] (t/app (k/const "Int.lt") a b))
(defn- le [a b] (t/app (k/const "Nat.le") a b))
(defn- close-at [a b eps]
  (t/app (c "Within") a b eps))
(defn- seq-value [s]
  (t/app (k/const "Subtype.val" u) sequence-type (c "Cauchy") s))

(defn- define! [name type value]
  (when-not (k/installed? (str prefix name))
    (t/install-declaration! :def (str prefix name) type value)))

(defn- theorem! [name type value]
  (when-not (k/installed? (str prefix name))
    (t/install-declaration! :thm (str prefix name) type value)))

(defn- within-self-proof [r eps positive]
  (let [d (den r)
        index (t/app (k/const "Prod.snd" level/zero level/zero) k/int-type nat r)
        dp (t/app (k/const "Int.ofNat_succ_pos") index)
        square-positive (t/app (k/const "Int.mul_pos") d d dp dp)
        bound (k/mul (num eps) (k/mul d d))
        bp (t/app (k/const "Int.mul_pos") (num eps) (k/mul d d) positive square-positive)
        left (lt (k/neg bound) k/zero)
        right (lt k/zero bound)
        at-zero (t/app (k/const "And.intro") left right
                       (t/app (k/const "Int.neg_neg_of_pos") bound bp) bp)
        difference (k/mul (k/sub (k/mul (num r) d) (k/mul (num r) d)) (den eps))
        p (algebra/prove-eq difference k/zero)
        motive (t/lambda [[x k/int-type]]
                 (t/and' (lt (k/neg bound) x) (lt x bound)))
        equality (k/congr-app motive nil (k/symm p)
                              {:dom k/int-type :cod t/prop :u u :v u})]
    (t/app (k/const "Eq.mp" level/zero)
           (:lhs equality) (:rhs equality) (:term equality) at-zero)))

(defn- cauchy-tail [s eps n]
  (t/forall [[i nat] [j nat]]
    (t/>-> (le n i)
           (le n j)
           (close-at (t/app s i) (t/app s j) eps))))

(defn install!
  "Installs the exact sequence/quotient carrier and quotient soundness theorem.
  Does not install or assume complete ordered field laws."
  []
  (k/ensure-init!)
  (locking k/install-lock
    (define! "RationalRep" t/type0 rep)
    (define! "Within" (t/>-> rep rep rep t/prop)
      (t/lambda [[a rep] [b rep] [eps rep]]
        (let [difference (k/mul (k/sub (k/mul (num a) (den b))
                                       (k/mul (num b) (den a))) (den eps))
              bound (k/mul (num eps) (k/mul (den a) (den b)))]
          (t/and' (lt (k/neg bound) difference) (lt difference bound)))))
    (define! "Cauchy" (t/predicate sequence-type)
      (t/lambda [[s sequence-type]]
        (t/forall [[eps rep]]
          (t/arrow (lt k/zero (num eps))
                   (t/exists' nat
                     (t/lambda [[n nat]] (cauchy-tail s eps n)))))))
    (define! "CauchySequence" t/type0
      (t/app (k/const "Subtype" u) sequence-type (c "Cauchy")))
    (theorem! "within_self"
      (t/forall [[r rep] [eps rep]]
        (t/arrow (lt k/zero (num eps)) (close-at r r eps)))
      (t/lambda [[r rep] [eps rep] [positive (lt k/zero (num eps))]]
        (within-self-proof r eps positive)))
    (define! "constantSequence" (t/arrow rep sequence-type)
      (t/lambda [[r rep]] (t/lam "n" nat (fn [_] r))))
    (theorem! "constant_cauchy"
      (t/forall [[r rep]] (t/app (c "Cauchy") (t/app (c "constantSequence") r)))
      (t/lambda [[r rep] [eps rep] [positive (lt k/zero (num eps))]]
        (let [s (t/app (c "constantSequence") r)
              predicate (t/lambda [[n nat]] (cauchy-tail s eps n))]
          (t/app (k/const "Exists.intro" u) nat predicate (e/lit-nat 0)
                 (t/lambda [[i nat] [j nat]
                            [_hi (le (e/lit-nat 0) i)]
                            [_hj (le (e/lit-nat 0) j)]]
                   (t/app (c "within_self") r eps positive))))))
    (define! "rationalSequence" (t/arrow rep (c "CauchySequence"))
      (t/lambda [[r rep]]
        (t/app (k/const "Subtype.mk" u) sequence-type (c "Cauchy")
               (t/app (c "constantSequence") r) (t/app (c "constant_cauchy") r))))
    (define! "Equivalent"
      (t/arrow (c "CauchySequence") (t/arrow (c "CauchySequence") t/prop))
      (t/lambda [[s (c "CauchySequence")] [r (c "CauchySequence")]]
        (t/forall [[eps rep]]
          (t/arrow (lt k/zero (num eps))
                   (t/exists' nat
                     (t/lambda [[n nat]]
                       (t/forall [[i nat]]
                         (t/arrow (le n i)
                                  (close-at (t/app (seq-value s) i)
                                            (t/app (seq-value r) i) eps)))))))))
    (define! "Carrier" t/type0
      (t/app (k/const "Quot" u) (c "CauchySequence") (c "Equivalent")))
    (define! "ofCauchy" (t/arrow (c "CauchySequence") (c "Carrier"))
      (t/app (k/const "Quot.mk" u) (c "CauchySequence") (c "Equivalent")))
    (define! "ofRationalRep" (t/arrow rep (c "Carrier"))
      (t/lambda [[r rep]] (t/app (c "ofCauchy") (t/app (c "rationalSequence") r))))
    (when-not (k/installed? (str prefix "sound"))
      (t/install-declaration!
       :thm (str prefix "sound")
       (t/forall [[s (c "CauchySequence")] [r (c "CauchySequence")]]
         (t/arrow (t/app (c "Equivalent") s r)
                  (t/app (k/const "Eq" u) (c "Carrier")
                         (t/app (c "ofCauchy") s) (t/app (c "ofCauchy") r))))
       (t/app (k/const "Quot.sound" u) (c "CauchySequence") (c "Equivalent")))))
  :installed)
