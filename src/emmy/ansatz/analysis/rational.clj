#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.rational
  "First proof layer for rational representatives.

  A representative is an integer numerator and a positive integer denominator.
  The executable operations below are exact host arithmetic. `arithmetic-laws`
  separately constructs kernel proofs of cross-multiplied ring identities over
  arbitrary integer representatives.

  [[install!]] adds the kernel layer, all checked by `check-constant`:

  ```
  Emmy.Analysis.Rational.Rep := {p : Int × Int // 0 < p.2}
  num, den, den_pos : ∀ r, 0 < den r
  Equiv a b := num a * den b = num b * den a
  add, mul, neg                 -- representative arithmetic
  int_mul_right_cancel : 0 < d → a * d = b * d → a = b
  equiv_refl, equiv_symm, equiv_trans
  add_congr, mul_congr, neg_congr
  ```

  Cancellation is derived from Init's `Int.mul_ediv_cancel`. This is still
  not a quotient construction, a proof of normalization, or an ordered field.
  No real-number axioms are added."
  (:refer-clojure :exclude [num])
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.level :as level]
            [emmy.ansatz.algebra :as algebra]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]))

(defn representative
  "Returns a reduced [numerator denominator] with positive denominator.
  Rejects inexact inputs and division by zero. Normalization is not yet proved
  in the kernel."
  [n d]
  (when-not (and (integer? n) (integer? d) (not (zero? d)))
    (throw (ex-info "Expected integer numerator and nonzero integer denominator"
                    {:numerator n :denominator d})))
  (let [n (bigint n)
        d (bigint d)
        gcd (loop [a (abs n) b (abs d)]
              (if (zero? b) a (recur b (mod a b))))
        sign (if (neg? d) -1 1)]
    [(*' sign (quot n gcd)) (quot (abs d) gcd)]))

(defn- checked [[n d :as r]]
  (when-not (and (= 2 (count r)) (integer? n) (integer? d) (pos? d))
    (throw (ex-info "Invalid rational representative" {:representative r})))
  r)

(defn equivalent?
  "Exact cross-multiplication relation on valid representatives."
  [a b]
  (let [[an ad] (checked a) [bn bd] (checked b)]
    (= (*' an bd) (*' bn ad))))

(defn add [a b]
  (let [[an ad] (checked a) [bn bd] (checked b)]
    (representative (+' (*' an bd) (*' bn ad)) (*' ad bd))))

(defn multiply [a b]
  (let [[an ad] (checked a) [bn bd] (checked b)]
    (representative (*' an bn) (*' ad bd))))

(defn negate [a]
  (let [[n d] (checked a)] (representative (-' n) d)))

(defn- pair-add [[an ad] [bn bd]]
  [(k/add (k/mul an bd) (k/mul bn ad)) (k/mul ad bd)])

(defn- pair-mul [[an ad] [bn bd]]
  [(k/mul an bn) (k/mul ad bd)])

(defn arithmetic-laws
  "Builds closed kernel proofs for representative ring identities.
  Every result contains the full :statement and :proof, checked before return.
  These identities alone do not establish the quotient or its field laws."
  []
  (k/ensure-init!)
  (let [vars (k/fresh-vars '[an ad bn bd cn cd])
        {an 'an ad 'ad bn 'bn bd 'bd cn 'cn cd 'cd} (into {} vars)
        a [an ad] b [bn bd] c [cn cd]
        identities {:add-comm [(pair-add a b) (pair-add b a)]
                    :add-assoc [(pair-add (pair-add a b) c)
                                (pair-add a (pair-add b c))]
                    :mul-comm [(pair-mul a b) (pair-mul b a)]
                    :mul-assoc [(pair-mul (pair-mul a b) c)
                                (pair-mul a (pair-mul b c))]
                    :distrib [(pair-mul a (pair-add b c))
                              (pair-add (pair-mul a b) (pair-mul a c))]
                    :add-zero [(pair-add a [k/zero (k/lit 1)]) a]
                    :mul-one [(pair-mul a [(k/lit 1) (k/lit 1)]) a]
                    :add-neg [(pair-add a [(k/neg an) ad])
                              [k/zero (k/lit 1)]]}]
    (into {}
          (for [[law [[ln ld] [rn rd]]] identities]
            (let [{:keys [statement proof] :as result}
                  (k/close vars (algebra/prove-eq (k/mul ln rd) (k/mul rn ld)))]
              (when-not (env/verifies? (k/env) statement proof)
                (throw (ex-info "Kernel rejected rational representative law"
                                {:law law})))
              [law result])))))

;; ## Kernel layer

(def ^:private l0 level/zero)
(def ^:private l1 (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.Rational.")
(defn- c [s] (k/const (str prefix s)))
(def ^:private int-pair (t/app (k/const "Prod" l0 l0) k/int-type k/int-type))

(defn lt
  "The kernel proposition `a < b` in `Int`."
  [a b]
  (t/app (k/const "LT.lt" l0) k/int-type (k/const "Int.instLTInt") a b))

(defn- positive-den [p]
  (lt k/zero (t/app (k/const "Prod.snd" l0 l0) k/int-type k/int-type p)))

(def ^:private rep-predicate (t/lambda [[p int-pair]] (positive-den p)))

(defn- int-div [a b]
  (t/app (k/const "HDiv.hDiv" l0 l0 l0) k/int-type k/int-type k/int-type
         (t/app (k/const "instHDiv" l0) k/int-type (k/const "Int.instDiv")) a b))

(defn- num [r] (t/app (c "num") r))
(defn- den [r] (t/app (c "den") r))
(defn equiv
  "The kernel proposition `Emmy.Analysis.Rational.Equiv a b`."
  [a b]
  (t/app (c "Equiv") a b))

(defn- hyp
  "Proof map for a hypothesis `h : Equiv a b`, i.e. `num a * den b = num b * den a`."
  [a b h]
  {:lhs (k/mul (num a) (den b)) :rhs (k/mul (num b) (den a)) :term h})

(defn make-rep
  "The kernel term `⟨(n, d), proof⟩ : Emmy.Analysis.Rational.Rep`, given a
  kernel proof `proof : 0 < d`."
  [n d proof]
  (t/app (k/const "Subtype.mk" l1) int-pair rep-predicate
         (t/app (k/const "Prod.mk" l0 l0) k/int-type k/int-type n d)
         proof))

(defn- mul-pos [a b ha hb]
  (t/app (k/const "Int.mul_pos") a b ha hb))

(defn- define! [label type value]
  (when-not (k/installed? (str prefix label))
    (t/install-declaration! :def (str prefix label) type value)))

(defn- theorem! [label type value]
  (when-not (k/installed? (str prefix label))
    (t/install-declaration! :thm (str prefix label) type value)))

(defn- cancel-proof
  "Proof of `a = b` from `hd : 0 < d` and `h : a * d = b * d`."
  [a b d hd h]
  (let [hne (t/app (k/const "Int.ne_of_gt") d k/zero hd)
        divide (t/lambda [[x k/int-type]] (int-div x d))
        step {:lhs (int-div (k/mul a d) d) :rhs (int-div (k/mul b d) d)
              :term (t/app (k/const "congrArg" l1 l1) k/int-type k/int-type
                           (k/mul a d) (k/mul b d) divide h)}]
    (:term (k/trans (k/symm (k/lemma "Int.mul_ediv_cancel" a d hne))
                    step
                    (k/lemma "Int.mul_ediv_cancel" b d hne)))))

(defn install!
  "Installs the kernel rational-representative layer (see the namespace
  docstring). Idempotent; requires only the bundled Init tier."
  []
  (k/ensure-init!)
  (locking k/install-lock
    (let [rep (c "Rep")]
      (define! "Rep" t/type0 (t/app (k/const "Subtype" l1) int-pair rep-predicate))
      (define! "num" (t/arrow rep k/int-type)
        (t/lambda [[r rep]]
          (t/app (k/const "Prod.fst" l0 l0) k/int-type k/int-type
                 (t/app (k/const "Subtype.val" l1) int-pair rep-predicate r))))
      (define! "den" (t/arrow rep k/int-type)
        (t/lambda [[r rep]]
          (t/app (k/const "Prod.snd" l0 l0) k/int-type k/int-type
                 (t/app (k/const "Subtype.val" l1) int-pair rep-predicate r))))
      (theorem! "den_pos" (t/forall [[r rep]] (lt k/zero (den r)))
        (t/lambda [[r rep]]
          (t/app (k/const "Subtype.property" l1) int-pair rep-predicate r)))
      (define! "Equiv" (t/arrow rep (t/arrow rep t/prop))
        (t/lambda [[a rep] [b rep]]
          (k/eq (k/mul (num a) (den b)) (k/mul (num b) (den a)))))
      (define! "add" (t/arrow rep (t/arrow rep rep))
        (t/lambda [[a rep] [b rep]]
          (make-rep (k/add (k/mul (num a) (den b)) (k/mul (num b) (den a)))
                    (k/mul (den a) (den b))
                    (mul-pos (den a) (den b)
                             (t/app (c "den_pos") a) (t/app (c "den_pos") b)))))
      (define! "mul" (t/arrow rep (t/arrow rep rep))
        (t/lambda [[a rep] [b rep]]
          (make-rep (k/mul (num a) (num b)) (k/mul (den a) (den b))
                    (mul-pos (den a) (den b)
                             (t/app (c "den_pos") a) (t/app (c "den_pos") b)))))
      (define! "neg" (t/arrow rep rep)
        (t/lambda [[a rep]]
          (make-rep (k/neg (num a)) (den a) (t/app (c "den_pos") a))))

      (theorem! "int_mul_right_cancel"
        (t/forall [[a k/int-type] [b k/int-type] [d k/int-type]]
          (t/arrow (lt k/zero d)
                   (t/arrow (k/eq (k/mul a d) (k/mul b d)) (k/eq a b))))
        (t/lambda [[a k/int-type] [b k/int-type] [d k/int-type]
                   [hd (lt k/zero d)] [h (k/eq (k/mul a d) (k/mul b d))]]
          (cancel-proof a b d hd h)))

      (theorem! "equiv_refl" (t/forall [[a rep]] (equiv a a))
        (t/lambda [[a rep]] (:term (k/refl (k/mul (num a) (den a))))))

      (theorem! "equiv_symm"
        (t/forall [[a rep] [b rep]] (t/arrow (equiv a b) (equiv b a)))
        (t/lambda [[a rep] [b rep] [h (equiv a b)]] (:term (k/symm (hyp a b h)))))

      (theorem! "equiv_trans"
        (t/forall [[a rep] [b rep] [cc rep]]
          (t/arrow (equiv a b) (t/arrow (equiv b cc) (equiv a cc))))
        (t/lambda [[a rep] [b rep] [cc rep] [h1 (equiv a b)] [h2 (equiv b cc)]]
          ;; (num a · den c) · den b = (num c · den a) · den b, then cancel den b.
          (let [lhs (k/mul (num a) (den cc))
                rhs (k/mul (num cc) (den a))
                scaled (algebra/linear-combination
                        (k/mul lhs (den b)) (k/mul rhs (den b))
                        [[(den cc) (hyp a b h1)] [(den a) (hyp b cc h2)]])]
            (t/app (c "int_mul_right_cancel") lhs rhs (den b)
                   (t/app (c "den_pos") b) (:term scaled)))))

      (theorem! "add_congr"
        (t/forall [[a rep] [a' rep] [b rep] [b' rep]]
          (t/arrow (equiv a a') (t/arrow (equiv b b')
                                         (equiv (t/app (c "add") a b) (t/app (c "add") a' b')))))
        (t/lambda [[a rep] [a' rep] [b rep] [b' rep] [ha (equiv a a')] [hb (equiv b b')]]
          (:term (algebra/linear-combination
                  (k/mul (k/add (k/mul (num a) (den b)) (k/mul (num b) (den a)))
                         (k/mul (den a') (den b')))
                  (k/mul (k/add (k/mul (num a') (den b')) (k/mul (num b') (den a')))
                         (k/mul (den a) (den b)))
                  [[(k/mul (den b) (den b')) (hyp a a' ha)]
                   [(k/mul (den a) (den a')) (hyp b b' hb)]]))))

      (theorem! "mul_congr"
        (t/forall [[a rep] [a' rep] [b rep] [b' rep]]
          (t/arrow (equiv a a') (t/arrow (equiv b b')
                                         (equiv (t/app (c "mul") a b) (t/app (c "mul") a' b')))))
        (t/lambda [[a rep] [a' rep] [b rep] [b' rep] [ha (equiv a a')] [hb (equiv b b')]]
          (:term (algebra/linear-combination
                  (k/mul (k/mul (num a) (num b)) (k/mul (den a') (den b')))
                  (k/mul (k/mul (num a') (num b')) (k/mul (den a) (den b)))
                  [[(k/mul (num b) (den b')) (hyp a a' ha)]
                   [(k/mul (num a') (den a)) (hyp b b' hb)]]))))

      (theorem! "neg_congr"
        (t/forall [[a rep] [a' rep]]
          (t/arrow (equiv a a') (equiv (t/app (c "neg") a) (t/app (c "neg") a'))))
        (t/lambda [[a rep] [a' rep] [ha (equiv a a')]]
          (:term (algebra/linear-combination
                  (k/mul (k/neg (num a)) (den a'))
                  (k/mul (k/neg (num a')) (den a))
                  [[(k/lit -1) (hyp a a' ha)]]))))))
  :installed)
