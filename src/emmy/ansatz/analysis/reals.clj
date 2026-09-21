#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.reals
  "ℝ as a quotient of Cauchy sequences of ℚ in the Ansatz kernel.

  ```
  Emmy.Analysis.R.Seq    := Nat → Q
  Emmy.Analysis.R.Cauchy s := ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → |s m − s n| < ε
  Emmy.Analysis.R.CSeq   := {s : Seq // Cauchy s}
  Emmy.Analysis.R.Equiv s t := ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |s n − t n| < ε
  equiv_refl, equiv_symm, equiv_trans
  Emmy.Analysis.R.R      := Quot CSeq Equiv,   ofQ : Q → R
  ```

  ε-N arguments split ε with `Q.half` and combine thresholds as `N₁ + N₂`.
  This supersedes the provisional `emmy.ansatz.analysis.real`, which is built
  on `Int × Nat` representatives rather than on `Q`."
  (:refer-clojure :exclude [abs])
  (:require [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.qfield :as q]
            [emmy.ansatz.core :as k]))

(def ^:private l0 level/zero)
(def ^:private l1 (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.R.")
(defn- c [s] (k/const (str prefix s)))
(defn- qc [s] (k/const (str "Emmy.Analysis.Q." s)))

(def Nat (k/const "Nat"))
(def Q q/Q)
(def Seq "The kernel type `Nat → Q`." (t/arrow Nat Q))

(defn- theorem! [label type proof]
  (when-not (k/installed? (str prefix label))
    (t/install-declaration! :thm (str prefix label) type proof)))

(defn- define! [label type value]
  (when-not (k/installed? (str prefix label))
    (t/install-declaration! :def (str prefix label) type value)))

;; ## Terms

(defn nat-le [m n] (t/app (k/const "LE.le" l0) Nat (k/const "instLENat") m n))
(defn nat-add [m n]
  (t/app (k/const "HAdd.hAdd" l0 l0 l0) Nat Nat Nat
         (t/app (k/const "instHAdd" l0) Nat (k/const "instAddNat")) m n))

(defn dist "`|p − q|` in `Q`." [p q] (q/abs (q/sub p q)))
(defn cauchy [s] (t/app (c "Cauchy") s))
(def CSeq (c "CSeq"))
(defn val' "The sequence underlying `s : CSeq`." [s] (t/app (k/const "Subtype.val" l1) Seq (c "Cauchy") s))
(defn at [s n] (t/app (val' s) n))
(defn equiv [s t] (t/app (c "Equiv") s t))
(def R (c "R"))

(defn- implies [& props] (reduce (fn [acc p] (t/arrow p acc)) (last props) (reverse (butlast props))))
(defn- pos [e] (q/lt q/zero e))

(defn eventually
  "`∃ N, ∀ n, N ≤ n → P n`, with `P` a function from a `Nat` term to a
  proposition."
  [P]
  (t/exists' Nat
    (t/lambda [[N Nat]]
      (t/forall [[n Nat]]
        (t/arrow (nat-le N n) (P n))))))

(defn- eventually-intro
  "Proof of `eventually P` from the threshold `N` and `f : ∀ n, N ≤ n → P n`."
  [P N f]
  (let [tail-property (t/lambda [[M Nat]]
                        (t/forall [[n Nat]]
                          (t/arrow (nat-le M n) (P n))))]
    (t/exists-intro Nat tail-property N f)))

(defn- eventually-elim
  "Proof of `goal` from `h : eventually P` and `k : ∀ N, (∀ n, N ≤ n → P n) → goal`
  (given as a Clojure function of the bound `N` and hypothesis)."
  [P goal h f]
  (let [body (fn [N] (t/forall [[n Nat]] (t/arrow (nat-le N n) (P n))))]
    (t/exists-elim Nat (t/lambda [[N Nat]] (body N)) goal h
                   (t/lambda [[N Nat] [hN (body N)]] (f N hN)))))

;; ## Metric helpers in Q

(defn- dist-self-lt
  "Proof of `|x − x| < ε` from `h : 0 < ε`."
  [x eps h]
  ;; |x − x| = |0| = 0
  (let [e1 (t/app (k/const "congrArg" l1 l1) Q Q (q/sub x x) q/zero (qc "abs") (t/app (qc "sub_self") x))
        e (t/app (k/const "Eq.trans" l1) Q (q/abs (q/sub x x)) (q/abs q/zero) q/zero e1 (qc "abs_zero"))]
    (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt z eps)) q/zero (q/abs (q/sub x x))
                    (t/app (k/const "Eq.symm" l1) Q (q/abs (q/sub x x)) q/zero e) h)))

(defn- half-split
  "Proof of `d₁ + d₂ < ε` from `a : d₁ < ε/2` and `b : d₂ < ε/2`."
  [d1 d2 eps a b]
  (let [e2 (q/mul q/half eps)
        sum (t/app (qc "add_lt_add") d1 e2 d2 e2 a b)]
    (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt (q/add d1 d2) z)) (q/add e2 e2) eps
                    (t/app (qc "half_add_half") eps) sum)))

(defn- threshold-le
  "Proofs of `N₁ ≤ n` and `N₂ ≤ n` from `h : N₁ + N₂ ≤ n`."
  [N1 N2 n h]
  (let [N (nat-add N1 N2)]
    [(t/app (k/const "Nat.le_trans") N1 N n (t/app (k/const "Nat.le_add_right") N1 N2) h)
     (t/app (k/const "Nat.le_trans") N2 N n (t/app (k/const "Nat.le_add_left") N2 N1) h)]))

;; ## Cauchy sequences: pointwise operations

(defn- cauchy-body
  "`∀ m n, N ≤ m → N ≤ n → |f m − f n| < ε`."
  [f eps N]
  (t/forall [[m Nat] [n Nat]]
    (implies (nat-le N m) (nat-le N n) (q/lt (dist (t/app f m) (t/app f n)) eps))))

(defn- cauchy-elim
  "Proof of `goal` from `h : ∃ N, cauchy-body f ε N` and `f'` (N, hN) ↦ proof."
  [f eps goal h k]
  (t/exists-elim Nat (t/lambda [[N Nat]] (cauchy-body f eps N)) goal h
                 (t/lambda [[N Nat] [hN (cauchy-body f eps N)]] (k N hN))))

(defn- cauchy-intro [f eps N proof]
  (t/exists-intro Nat (t/lambda [[M Nat]] (cauchy-body f eps M)) N proof))

(defn cauchy-of "`s.property : Cauchy (val s)`." [s]
  (t/app (k/const "Subtype.property" l1) Seq (c "Cauchy") s))

(defn- make-cseq [f proof]
  (t/app (k/const "Subtype.mk" l1) Seq (c "Cauchy") f proof))

(defn- binary-cauchy-proof
  "Proof of `Cauchy (op f g)` for a pointwise `op` whose distance is bounded
  by the sum of the two distances (`dist-le` builds that bound at indices m n)."
  [f g hf hg op-seq dist-le]
  (t/lambda [[eps Q] [he (pos eps)]]
    (let [e2 (q/mul q/half eps)
          he2 (t/app (qc "half_pos_of_pos") eps he)
          h (op-seq f g)
          goal (t/exists' Nat (t/lambda [[N Nat]] (cauchy-body h eps N)))]
      (cauchy-elim f e2 goal (t/app hf e2 he2)
                   (fn [N1 hN1]
                     (cauchy-elim g e2 goal (t/app hg e2 he2)
                                  (fn [N2 hN2]
                                    (cauchy-intro h eps (nat-add N1 N2)
                                                  (t/lambda [[m Nat] [n Nat]
                                                             [hm (nat-le (nat-add N1 N2) m)]
                                                             [hn (nat-le (nat-add N1 N2) n)]]
                                                    (let [[hm1 hm2] (threshold-le N1 N2 m hm)
                                                          [hn1 hn2] (threshold-le N1 N2 n hn)
                                                          d1 (dist (t/app f m) (t/app f n))
                                                          d2 (dist (t/app g m) (t/app g n))
                                                          sum (half-split d1 d2 eps
                                                                          (t/app hN1 m n hm1 hn1)
                                                                          (t/app hN2 m n hm2 hn2))]
                                                      (t/app (qc "lt_of_le_of_lt")
                                                             (dist (t/app h m) (t/app h n)) (q/add d1 d2) eps
                                                             (dist-le m n) sum)))))))))))

(defn- binary-congr-proof
  "Proof of `op s t ≈ op s' t'` from `hs : s ≈ s'` and `ht : t ≈ t'`, where the
  distance of the results at index n is bounded by `dist-le n`."
  [s s' t t' hs ht at-op dist-le]
  (t/lambda [[eps Q] [he (pos eps)]]
    (let [e2 (q/mul q/half eps)
          he2 (t/app (qc "half_pos_of_pos") eps he)
          P1 #(q/lt (dist (at s %) (at s' %)) e2)
          P2 #(q/lt (dist (at t %) (at t' %)) e2)
          P #(q/lt (dist (at-op s t %) (at-op s' t' %)) eps)]
      (eventually-elim P1 (eventually P) (t/app hs e2 he2)
                       (fn [N1 hN1]
                         (eventually-elim P2 (eventually P) (t/app ht e2 he2)
                                          (fn [N2 hN2]
                                            (eventually-intro P (nat-add N1 N2)
                                                              (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                (let [[hn1 hn2] (threshold-le N1 N2 n hn)
                                                                      d1 (dist (at s n) (at s' n))
                                                                      d2 (dist (at t n) (at t' n))
                                                                      sum (half-split d1 d2 eps (t/app hN1 n hn1) (t/app hN2 n hn2))]
                                                                  (t/app (qc "lt_of_le_of_lt")
                                                                         (dist (at-op s t n) (at-op s' t' n)) (q/add d1 d2) eps
                                                                         (dist-le n) sum)))))))))))

(defn- rewrite-lt-left
  "Proof of `y < ε` from `h : x < ε` and `e : x = y` in `Q`."
  [x y eps e h]
  (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt z eps)) x y e h))

(defn- rewrite-lt-right
  "Proof of `z < y` from `h : z < x` and `e : x = y` in `Q`."
  [x y z e h]
  (t/transport-at Q l1 (t/lambda [[w Q]] (q/lt z w)) x y e h))

(def qconf
  "Quotient description of `R` for the generic lifting helpers."
  {:alpha (c "CSeq") :rel (c "Equiv")
   :refl #(t/app (c "equiv_refl") %)
   :symm #(t/app (c "equiv_symm") %1 %2 %3)})

(defn add [x y] (t/app (c "add") x y))
(defn neg [x] (t/app (c "neg") x))
(defn sub [x y] (t/app (c "sub") x y))
(defn of-q [x] (t/app (c "ofQ") x))
(def zero (c "zero"))
(def one (c "one"))

(defn- install-add-neg! []
  (define! "addSeq" (t/arrow Seq (t/arrow Seq Seq))
    (t/lambda [[f Seq] [g Seq]] (t/lam "n" Nat #(q/add (t/app f %) (t/app g %)))))
  (define! "negSeq" (t/arrow Seq Seq)
    (t/lambda [[f Seq]] (t/lam "n" Nat #(q/neg (t/app f %)))))
  (let [add-seq #(t/app (c "addSeq") %1 %2)
        neg-seq #(t/app (c "negSeq") %)]
    (theorem! "add_cauchy"
      (t/forall [[f Seq] [g Seq]] (implies (cauchy f) (cauchy g) (cauchy (add-seq f g))))
      (t/lambda [[f Seq] [g Seq] [hf (cauchy f)] [hg (cauchy g)]]
        (binary-cauchy-proof f g hf hg add-seq
                             (fn [m n] (t/app (qc "dist_add_le") (t/app f m) (t/app g m) (t/app f n) (t/app g n))))))
    (theorem! "neg_cauchy"
      (t/forall [[f Seq]] (implies (cauchy f) (cauchy (neg-seq f))))
      (t/lambda [[f Seq] [hf (cauchy f)] [eps Q] [he (pos eps)]]
        (let [h (neg-seq f)
              goal (t/exists' Nat (t/lambda [[N Nat]] (cauchy-body h eps N)))]
          (cauchy-elim f eps goal (t/app hf eps he)
                       (fn [N hN]
                         (cauchy-intro h eps N
                                       (t/lambda [[m Nat] [n Nat] [hm (nat-le N m)] [hn (nat-le N n)]]
                                         (rewrite-lt-left (dist (t/app f m) (t/app f n)) (dist (t/app h m) (t/app h n)) eps
                                                          (t/app (k/const "Eq.symm" l1) Q
                                                                 (dist (t/app h m) (t/app h n)) (dist (t/app f m) (t/app f n))
                                                                 (t/app (qc "dist_neg") (t/app f m) (t/app f n)))
                                                          (t/app hN m n hm hn)))))))))
    (define! "cadd" (t/arrow CSeq (t/arrow CSeq CSeq))
      (t/lambda [[s CSeq] [u CSeq]]
        (make-cseq (add-seq (val' s) (val' u))
                   (t/app (c "add_cauchy") (val' s) (val' u) (cauchy-of s) (cauchy-of u)))))
    (define! "cneg" (t/arrow CSeq CSeq)
      (t/lambda [[s CSeq]] (make-cseq (neg-seq (val' s)) (t/app (c "neg_cauchy") (val' s) (cauchy-of s)))))
    (let [at-add (fn [s u n] (q/add (at s n) (at u n)))
          cadd #(t/app (c "cadd") %1 %2)
          cneg #(t/app (c "cneg") %)]
      (theorem! "add_congr"
        (t/forall [[s CSeq] [s' CSeq] [u CSeq] [u' CSeq]]
          (implies (equiv s s') (equiv u u') (equiv (cadd s u) (cadd s' u'))))
        (t/lambda [[s CSeq] [s' CSeq] [u CSeq] [u' CSeq] [hs (equiv s s')] [hu (equiv u u')]]
          (binary-congr-proof s s' u u' hs hu at-add
                              (fn [n] (t/app (qc "dist_add_le") (at s n) (at u n) (at s' n) (at u' n))))))
      (theorem! "neg_congr"
        (t/forall [[s CSeq] [s' CSeq]] (implies (equiv s s') (equiv (cneg s) (cneg s'))))
        (t/lambda [[s CSeq] [s' CSeq] [hs (equiv s s')] [eps Q] [he (pos eps)]]
          (let [P #(q/lt (dist (at s %) (at s' %)) eps)
                P' #(q/lt (dist (q/neg (at s %)) (q/neg (at s' %))) eps)]
            (eventually-elim P (eventually P') (t/app hs eps he)
                             (fn [N hN]
                               (eventually-intro P' N
                                                 (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                   (rewrite-lt-left (dist (at s n) (at s' n))
                                                                    (dist (q/neg (at s n)) (q/neg (at s' n))) eps
                                                                    (t/app (k/const "Eq.symm" l1) Q
                                                                           (dist (q/neg (at s n)) (q/neg (at s' n)))
                                                                           (dist (at s n) (at s' n))
                                                                           (t/app (qc "dist_neg") (at s n) (at s' n)))
                                                                    (t/app hN n hn)))))))))
      (define! "add" (t/arrow R (t/arrow R R))
        (t/lift2* qconf cadd (fn [a a' b b' ha hb] (t/app (c "add_congr") a a' b b' ha hb))))
      (define! "neg" (t/arrow R R)
        (t/lift1* qconf cneg (fn [a b h] (t/app (c "neg_congr") a b h))))
      (define! "sub" (t/arrow R (t/arrow R R))
        (t/lambda [[x R] [y R]] (add x (neg y))))
      (define! "zero" R (of-q q/zero))
      (define! "one" R (of-q q/one)))))

;; ## Boundedness and multiplication

(defn nat-lt [m n] (t/app (k/const "LT.lt" l0) Nat (k/const "instLTNat") m n))

(defn- bound-below
  "`0 < B ∧ ∀ n, n < N → |f n| < B`."
  [f N B]
  (t/and' (pos B) (t/forall [[n Nat]] (t/arrow (nat-lt n N) (q/lt (q/abs (t/app f n)) B)))))

(defn- bound-body
  "`0 < B ∧ ∀ n, |f n| < B`."
  [f B]
  (t/and' (pos B) (t/forall [[n Nat]] (q/lt (q/abs (t/app f n)) B))))

(defn- bounded [f] (t/exists' Q (t/lambda [[B Q]] (bound-body f B))))

(defn- with-bound
  "Proof of `goal` from `hf : Cauchy f` and `k`, called with the bound `B`, a
  proof of `0 < B` and a function from `n` to a proof of `|f n| < B`."
  [f hf goal k]
  (let [all (fn [B] (t/forall [[n Nat]] (q/lt (q/abs (t/app f n)) B)))]
    (t/exists-elim Q (t/lambda [[B Q]] (bound-body f B)) goal (t/app (c "bounded") f hf)
                   (t/lambda [[B Q] [hB (bound-body f B)]]
                     (k B (t/and-left (pos B) (all B) hB)
                        (fn [n] (t/app (t/and-right (pos B) (all B) hB) n)))))))

(defn- product-close
  "Proof of `|a·c − b·d| < ε` from `hA : |a| < A`, `hD : |d| < D` (with `A`,
  `D` positive), `hcd : |c − d| < A⁻¹·(ε/2)` and `hab : |a − b| < D⁻¹·(ε/2)`."
  [a b cc d A D eps hA hApos hD hDpos hcd hab]
  (let [e2 (q/mul q/half eps)
        dA (q/mul (q/inv A) e2) dD (q/mul (q/inv D) e2)
        x1 (q/mul (q/abs a) (dist cc d))
        x2 (q/mul (q/abs d) (dist a b))
        close (fn [x bound-prop hx hxb dist-nonneg hdist B dB hBpos]
                (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt bound-prop z)) (q/mul B dB) e2
                                (t/app (qc "mul_inv_mul") B e2 hBpos)
                                (t/app (qc "mul_lt_of_lt_of_lt") (q/abs x) B hx dB
                                       (t/app (qc "abs_nonneg") x) hxb dist-nonneg hdist)))
        t1 (close a x1 (dist cc d) hA (t/app (qc "abs_nonneg") (q/sub cc d)) hcd A dA hApos)
        t2 (close d x2 (dist a b) hD (t/app (qc "abs_nonneg") (q/sub a b)) hab D dD hDpos)]
    (t/app (qc "lt_of_le_of_lt") (dist (q/mul a cc) (q/mul b d)) (q/add x1 x2) eps
           (t/app (qc "dist_mul_le") a b cc d)
           (half-split x1 x2 eps t1 t2))))

(defn- tolerance-pos
  "Proof of `0 < B⁻¹·(ε/2)` from `0 < B` and `0 < ε`."
  [B eps hB he]
  (t/app (qc "mul_pos") (q/inv B) (q/mul q/half eps)
         (t/app (qc "inv_pos") B hB) (t/app (qc "half_pos_of_pos") eps he)))

(defn mul [x y] (t/app (c "mul") x y))

(defn- install-mul! []
  (let [one-pos (qc "zero_lt_one")]
    ;; ∀ N, ∃ B, 0 < B ∧ ∀ n < N, |f n| < B, by induction on N
    (theorem! "bounded_below"
      (t/forall [[f Seq] [N Nat]] (t/exists' Q (t/lambda [[B Q]] (bound-below f N B))))
      (t/lambda [[f Seq]]
        (let [pre (fn [N] (t/exists' Q (t/lambda [[B Q]] (bound-below f N B))))
              intro (fn [N B hpos hall]
                      (t/exists-intro Q (t/lambda [[B' Q]] (bound-below f N B')) B
                                      (t/and-intro (pos B) (t/forall [[n Nat]] (t/arrow (nat-lt n N) (q/lt (q/abs (t/app f n)) B)))
                                                   hpos hall)))
              base (intro (k/const "Nat.zero") q/one one-pos
                          (t/lambda [[n Nat] [h (nat-lt n (k/const "Nat.zero"))]]
                            (t/false-elim (q/lt (q/abs (t/app f n)) q/one)
                                          (t/app (k/const "Nat.not_lt_zero") n h))))
              step (t/lambda [[K Nat] [ih (pre K)]]
                     (let [K' (t/app (k/const "Nat.succ") K)
                           all (fn [B] (t/forall [[n Nat]] (t/arrow (nat-lt n K) (q/lt (q/abs (t/app f n)) B))))]
                       (t/exists-elim Q (t/lambda [[B Q]] (bound-below f K B)) (pre K') ih
                                      (t/lambda [[B Q] [hB (bound-below f K B)]]
                                        (let [fK (q/abs (t/app f K))
                                              B' (q/add B fK)
                                              hpos (t/and-left (pos B) (all B) hB)
                                              hall (t/and-right (pos B) (all B) hB)
                                              le-B (t/app (qc "le_add_of_nonneg_right") B fK (t/app (qc "abs_nonneg") (t/app f K)))]
                                          (intro K' B'
                                                 (t/app (qc "lt_of_lt_of_le") q/zero B B' hpos le-B)
                                                 (t/lambda [[n Nat] [h (nat-lt n K')]]
                                                   (let [goal (q/lt (q/abs (t/app f n)) B')
                                                         hle (t/app (k/const "Nat.le_of_lt_succ") n K h)
                                                         eq-nk (t/app (k/const "Eq" l1) Nat n K)]
                                                     (t/or-elim eq-nk (nat-lt n K) goal
                                                                (t/app (k/const "Nat.eq_or_lt_of_le") n K hle)
                                                                (t/lam "e" eq-nk
                                                                       (fn [e]
                                                                         (t/transport-at Nat l1 (t/lambda [[z Nat]] (q/lt (q/abs (t/app f z)) B')) K n
                                                                                         (t/app (k/const "Eq.symm" l1) Nat n K e)
                                                                                         (t/app (qc "lt_add_of_pos_left") fK B hpos))))
                                                                (t/lam "hl" (nat-lt n K)
                                                                       (fn [hl]
                                                                         (t/app (qc "lt_of_lt_of_le") (q/abs (t/app f n)) B B'
                                                                                (t/app hall n hl) le-B))))))))))))]
          (t/lambda [[N Nat]]
            (t/app (k/const "Nat.rec" l0) (t/lambda [[M Nat]] (pre M)) base step N)))))
    ;; Cauchy sequences are bounded: below the Cauchy threshold for ε = 1 use
    ;; the finite bound, beyond it |f n| ≤ |f N| + |f n − f N| < |f N| + 1
    (theorem! "bounded"
      (t/forall [[f Seq]] (implies (cauchy f) (bounded f)))
      (t/lambda [[f Seq] [hf (cauchy f)]]
        (cauchy-elim f q/one (bounded f) (t/app hf q/one one-pos)
                     (fn [N hN]
                       (let [all0 (fn [B] (t/forall [[n Nat]] (t/arrow (nat-lt n N) (q/lt (q/abs (t/app f n)) B))))]
                         (t/exists-elim Q (t/lambda [[B Q]] (bound-below f N B)) (bounded f)
                                        (t/app (c "bounded_below") f N)
                                        (t/lambda [[B0 Q] [hB0 (bound-below f N B0)]]
                                          (let [fN (q/abs (t/app f N))
                                                C (q/add fN q/one)
                                                B (q/add B0 C)
                                                hB0pos (t/and-left (pos B0) (all0 B0) hB0)
                                                hall (t/and-right (pos B0) (all0 B0) hB0)
                                                hCpos (t/app (qc "lt_of_le_of_lt") q/zero fN C (t/app (qc "abs_nonneg") (t/app f N))
                                                             (t/app (qc "lt_add_of_pos_right") fN q/one one-pos))
                                                hC (t/app (qc "le_of_lt") q/zero C hCpos)
                                                le-B0 (t/app (qc "le_add_of_nonneg_right") B0 C hC)
                                                le-C (t/app (qc "le_add_of_nonneg_left") C B0 (t/app (qc "le_of_lt") q/zero B0 hB0pos))]
                                            (t/exists-intro Q (t/lambda [[B' Q]] (bound-body f B')) B
                                                            (t/and-intro (pos B) (t/forall [[n Nat]] (q/lt (q/abs (t/app f n)) B))
                                                                         (t/app (qc "lt_of_lt_of_le") q/zero B0 B hB0pos le-B0)
                                                                         (t/lambda [[n Nat]]
                                                                           (let [fn' (q/abs (t/app f n))
                                                                                 goal (q/lt fn' B)
                                                                                 ge (nat-le N n)]
                                                                             (t/or-elim (nat-lt n N) ge goal
                                                                                        (t/app (k/const "Nat.lt_or_ge") n N)
                                                                                        (t/lam "h" (nat-lt n N)
                                                                                               #(t/app (qc "lt_of_lt_of_le") fn' B0 B (t/app hall n %) le-B0))
                                                                                        (t/lam "h" ge
                                                                                               (fn [h]
                                                                                                 (let [d (dist (t/app f n) (t/app f N))
                                                                                                       s1 (t/app (qc "abs_le_add_dist") (t/app f n) (t/app f N))
                                                                                                       s2 (t/app (qc "add_lt_add_left") d q/one fN
                                                                                                                 (t/app hN n N h (t/app (k/const "Nat.le_refl") N)))
                                                                                                       s3 (t/app (qc "lt_of_le_of_lt") fn' (q/add fN d) C s1 s2)]
                                                                                                   (t/app (qc "lt_of_lt_of_le") fn' C B s3 le-C)))))))))))))))))
    (define! "mulSeq" (t/arrow Seq (t/arrow Seq Seq))
      (t/lambda [[f Seq] [g Seq]] (t/lam "n" Nat #(q/mul (t/app f %) (t/app g %)))))
    (let [mul-seq #(t/app (c "mulSeq") %1 %2)]
      (theorem! "mul_cauchy"
        (t/forall [[f Seq] [g Seq]] (implies (cauchy f) (cauchy g) (cauchy (mul-seq f g))))
        (t/lambda [[f Seq] [g Seq] [hf (cauchy f)] [hg (cauchy g)] [eps Q] [he (pos eps)]]
          (let [h (mul-seq f g)
                goal (t/exists' Nat (t/lambda [[N Nat]] (cauchy-body h eps N)))
                e2 (q/mul q/half eps)]
            (with-bound f hf goal
              (fn [Bf hBf bf]
                (with-bound g hg goal
                  (fn [Bg hBg bg]
                    (let [d1 (q/mul (q/inv Bf) e2) d2 (q/mul (q/inv Bg) e2)]
                      (cauchy-elim g d1 goal (t/app hg d1 (tolerance-pos Bf eps hBf he))
                                   (fn [N1 hN1]
                                     (cauchy-elim f d2 goal (t/app hf d2 (tolerance-pos Bg eps hBg he))
                                                  (fn [N2 hN2]
                                                    (cauchy-intro h eps (nat-add N1 N2)
                                                                  (t/lambda [[m Nat] [n Nat]
                                                                             [hm (nat-le (nat-add N1 N2) m)]
                                                                             [hn (nat-le (nat-add N1 N2) n)]]
                                                                    (let [[hm1 hm2] (threshold-le N1 N2 m hm)
                                                                          [hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                      (product-close (t/app f m) (t/app f n) (t/app g m) (t/app g n)
                                                                                     Bf Bg eps (bf m) hBf (bg n) hBg
                                                                                     (t/app hN1 m n hm1 hn1)
                                                                                     (t/app hN2 m n hm2 hn2)))))))))))))))))
      (define! "cmul" (t/arrow CSeq (t/arrow CSeq CSeq))
        (t/lambda [[s CSeq] [u CSeq]]
          (make-cseq (mul-seq (val' s) (val' u))
                     (t/app (c "mul_cauchy") (val' s) (val' u) (cauchy-of s) (cauchy-of u)))))
      (let [cmul #(t/app (c "cmul") %1 %2)]
        ;; |s u − s' u'| ≤ |s|·|u − u'| + |u'|·|s − s'|, with bounds on s and u'
        (theorem! "mul_congr"
          (t/forall [[s CSeq] [s' CSeq] [u CSeq] [u' CSeq]]
            (implies (equiv s s') (equiv u u') (equiv (cmul s u) (cmul s' u'))))
          (t/lambda [[s CSeq] [s' CSeq] [u CSeq] [u' CSeq] [hs (equiv s s')] [hu (equiv u u')] [eps Q] [he (pos eps)]]
            (let [P #(q/lt (dist (q/mul (at s %) (at u %)) (q/mul (at s' %) (at u' %))) eps)
                  goal (eventually P)
                  e2 (q/mul q/half eps)]
              (with-bound (val' s) (cauchy-of s) goal
                (fn [A hA ba]
                  (with-bound (val' u') (cauchy-of u') goal
                    (fn [D hD bd]
                      (let [d1 (q/mul (q/inv A) e2) d2 (q/mul (q/inv D) e2)
                            P1 #(q/lt (dist (at u %) (at u' %)) d1)
                            P2 #(q/lt (dist (at s %) (at s' %)) d2)]
                        (eventually-elim P1 goal (t/app hu d1 (tolerance-pos A eps hA he))
                                         (fn [N1 hN1]
                                           (eventually-elim P2 goal (t/app hs d2 (tolerance-pos D eps hD he))
                                                            (fn [N2 hN2]
                                                              (eventually-intro P (nat-add N1 N2)
                                                                                (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                                  (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                    (product-close (at s n) (at s' n) (at u n) (at u' n)
                                                                                                   A D eps (ba n) hA (bd n) hD
                                                                                                   (t/app hN1 n hn1)
                                                                                                   (t/app hN2 n hn2)))))))))))))))))
        (define! "mul" (t/arrow R (t/arrow R R))
          (t/lift2* qconf cmul (fn [a a' b b' ha hb] (t/app (c "mul_congr") a a' b b' ha hb))))))))

;; ## Ring laws
;;
;; Each law on `R` is a pointwise law in `Q`: pointwise equal sequences are
;; equivalent (`equiv_of_eq`), so `Quot.sound` gives the equality in `R`.

(defn- cconst "The constant Cauchy sequence at `x : Q`." [x]
  (make-cseq (t/app (c "constSeq") x) (t/app (c "const_cauchy") x)))
(defn- cadd [s u] (t/app (c "cadd") s u))
(defn- cneg [s] (t/app (c "cneg") s))
(defn- cmul [s u] (t/app (c "cmul") s u))
(defn- eq-r [x y] (k/eq-at R l1 x y))

(defn- r-law!
  "Installs `∀ x₁ … xₙ : R, lhs = rhs`. `r-lhs`/`r-rhs` build the sides from
  `R` terms and `c-lhs`/`c-rhs` from `CSeq` terms; `pointwise` maps the `CSeq`
  fvars and an index `n` to a proof of the `Q` equation at `n`."
  [label n r-lhs r-rhs c-lhs c-rhs pointwise]
  (let [names (map #(str "x" %) (range n))
        statement (fn [xs] (eq-r (apply r-lhs xs) (apply r-rhs xs)))]
    (theorem! label
      (q/pis names R statement)
      (q/lams names R
              (fn [xs]
                (t/quot-ind-all* qconf xs (fn [& ys] (statement ys))
                                 (fn [ss]
                                   (let [a (apply c-lhs ss) b (apply c-rhs ss)]
                                     (t/quot-sound CSeq (c "Equiv") a b
                                                   (t/app (c "equiv_of_eq") a b
                                                          (t/lam "n" Nat #(apply pointwise (conj ss %)))))))))))))

(defn ring-identity!
  "Installs a checked real ring identity from symbolic +, *, -, 0 and 1 forms.
  `vars` lists the symbols. The proof reduces through both quotient layers to
  an integer ring identity; this is not a trusted algebra oracle. Call install!
  first. Returns the real theorem constant."
  [label vars lhs rhs]
  (letfn [(interpret [ops bindings form]
            (cond
              (contains? bindings form) (get bindings form)
              (= form 0) (:zero ops)
              (= form 1) (:one ops)
              (seq? form)
              (let [[op & args] form
                    args (mapv #(interpret ops bindings %) args)]
                (case op
                  + (if (seq args) (reduce (:add ops) args) (:zero ops))
                  * (if (seq args) (reduce (:mul ops) args) (:one ops))
                  - (if (= 1 (count args)) ((:neg ops) (first args))
                        (reduce (fn [a b] ((:add ops) a ((:neg ops) b))) args))
                  (throw (ex-info "Unsupported ring operation" {:form form}))))
              :else (throw (ex-info "Unsupported ring atom" {:form form}))))
          (side [ops form]
            (fn [& args] (interpret ops (zipmap vars args) form)))]
    (let [qops {:add q/add :mul q/mul :neg q/neg :zero q/zero :one q/one}
          reps {:add q/radd :mul q/rmul :neg q/rneg :zero q/rzero :one q/rone}
          rops {:add add :mul mul :neg neg :zero zero :one one}
          seqs {:add cadd :mul cmul :neg cneg :zero (cconst q/zero) :one (cconst q/one)}
          qlabel (str "RealRing." label)]
      (q/quot-law! qlabel (count vars) (side qops lhs) (side qops rhs)
                    (side reps lhs) (side reps rhs))
      (r-law! label (count vars) (side rops lhs) (side rops rhs)
              (side seqs lhs) (side seqs rhs)
              (fn [& args]
                (apply t/app (qc qlabel) (map #(at % (last args)) (butlast args)))))
      (c label))))

(defn- install-ring-laws! []
  (theorem! "equiv_of_eq"
    (t/forall [[s CSeq] [u CSeq]]
      (implies (t/forall [[n Nat]] (k/eq-at Q l1 (at s n) (at u n))) (equiv s u)))
    (t/lambda [[s CSeq] [u CSeq] [h (t/forall [[n Nat]] (k/eq-at Q l1 (at s n) (at u n)))] [eps Q] [he (pos eps)]]
      (eventually-intro #(q/lt (dist (at s %) (at u %)) eps) (e/lit-nat 0)
                        (t/lambda [[n Nat] [_hn (nat-le (e/lit-nat 0) n)]]
                          (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt (dist (at s n) z) eps)) (at s n) (at u n)
                                          (t/app h n) (dist-self-lt (at s n) eps he))))))
  (let [qlaw (fn [nm] (fn [& args] (let [n (last args) ss (butlast args)]
                                     (apply t/app (qc nm) (map #(at % n) ss)))))
        cz (cconst q/zero) c1 (cconst q/one)]
    (r-law! "add_comm" 2 add #(add %2 %1) cadd #(cadd %2 %1) (qlaw "add_comm"))
    (r-law! "add_assoc" 3 #(add (add %1 %2) %3) #(add %1 (add %2 %3))
            #(cadd (cadd %1 %2) %3) #(cadd %1 (cadd %2 %3)) (qlaw "add_assoc"))
    (r-law! "zero_add" 1 #(add zero %) identity #(cadd cz %) identity (qlaw "zero_add"))
    (r-law! "add_left_neg" 1 #(add (neg %) %) (constantly zero) #(cadd (cneg %) %) (constantly cz)
            (qlaw "add_left_neg"))
    (r-law! "sub_self" 1 #(sub % %) (constantly zero) #(cadd % (cneg %)) (constantly cz) (qlaw "sub_self"))
    (r-law! "mul_comm" 2 mul #(mul %2 %1) cmul #(cmul %2 %1) (qlaw "mul_comm"))
    (r-law! "mul_assoc" 3 #(mul (mul %1 %2) %3) #(mul %1 (mul %2 %3))
            #(cmul (cmul %1 %2) %3) #(cmul %1 (cmul %2 %3)) (qlaw "mul_assoc"))
    (r-law! "one_mul" 1 #(mul one %) identity #(cmul c1 %) identity (qlaw "one_mul"))
    (r-law! "left_distrib" 3 #(mul %1 (add %2 %3)) #(add (mul %1 %2) (mul %1 %3))
            #(cmul %1 (cadd %2 %3)) #(cadd (cmul %1 %2) (cmul %1 %3)) (qlaw "left_distrib"))
    ;; ofQ is a ring homomorphism: both sides are pointwise identical
    (doseq [[label r-op q-op c-op] [["ofQ_add" add q/add cadd] ["ofQ_mul" mul q/mul cmul]]]
      (theorem! label
        (t/forall [[p Q] [u Q]] (eq-r (r-op (of-q p) (of-q u)) (of-q (q-op p u))))
        (t/lambda [[p Q] [u Q]]
          (let [a (c-op (cconst p) (cconst u)) b (cconst (q-op p u))]
            (t/quot-sound CSeq (c "Equiv") a b
                          (t/app (c "equiv_of_eq") a b
                                 (t/lam "n" Nat (fn [_] (t/app (k/const "Eq.refl" l1) Q (q-op p u))))))))))
    (theorem! "ofQ_neg"
      (t/forall [[p Q]] (eq-r (neg (of-q p)) (of-q (q/neg p))))
      (t/lambda [[p Q]]
        (let [a (cneg (cconst p)) b (cconst (q/neg p))]
          (t/quot-sound CSeq (c "Equiv") a b
                        (t/app (c "equiv_of_eq") a b
                               (t/lam "n" Nat (fn [_] (t/app (k/const "Eq.refl" l1) Q (q/neg p)))))))))))

;; ## Order
;;
;; `Pos s` says that `s` is eventually bounded below by some positive rational.
;; It respects `Equiv` (`pos_congr`, by `Q.close_lower` at ε/2), so it lifts to
;; `Positive : R → Prop`, and `x < y := Positive (y − x)`.

(defn- pos-body [f e N]
  (t/forall [[n Nat]] (t/arrow (nat-le N n) (q/lt e (t/app f n)))))

(defn- pos-seq
  "`∃ ε, 0 < ε ∧ ∃ N, ∀ n ≥ N, ε < f n`."
  [f]
  (t/exists' Q (t/lambda [[e Q]] (t/and' (pos e) (t/exists' Nat (t/lambda [[N Nat]] (pos-body f e N)))))))

(defn- pos-tail [f e] (t/exists' Nat (t/lambda [[N Nat]] (pos-body f e N))))

(defn- pos-intro
  "Proof of `pos-seq f` from the witness `ε`, `hp : 0 < ε`, threshold `N` and
  `hall : ∀ n ≥ N, ε < f n`."
  [f e N hp hall]
  (t/exists-intro Q (t/lambda [[e' Q]] (t/and' (pos e') (pos-tail f e'))) e
                  (t/and-intro (pos e) (pos-tail f e) hp
                               (t/exists-intro Nat (t/lambda [[M Nat]] (pos-body f e M)) N hall))))

(defn- pos-elim
  "Proof of `goal` from `h : pos-seq f`, with `k` called on the witness `ε`, a
  proof of `0 < ε`, the threshold `N` and `hN : ∀ n ≥ N, ε < f n`."
  [f goal h k]
  (let [inner (fn [e] (t/and' (pos e) (pos-tail f e)))]
    (t/exists-elim Q (t/lambda [[e Q]] (inner e)) goal h
                   (t/lambda [[e Q] [hA (inner e)]]
                     (t/exists-elim Nat (t/lambda [[N Nat]] (pos-body f e N)) goal
                                    (t/and-right (pos e) (pos-tail f e) hA)
                                    (t/lambda [[N Nat] [hN (pos-body f e N)]]
                                      (k e (t/and-left (pos e) (pos-tail f e) hA) N hN)))))))

(defn positive [x] (t/app (c "Positive") x))
(defn lt [x y] (t/app (c "lt") x y))
(defn le [x y] (t/app (c "le") x y))

(defn- install-order! []
  (define! "Pos" (t/arrow CSeq t/prop) (t/lambda [[s CSeq]] (pos-seq (val' s))))
  (let [Pos #(t/app (c "Pos") %)]
    (theorem! "pos_congr"
      (t/forall [[s CSeq] [u CSeq]] (implies (equiv s u) (Pos s) (Pos u)))
      (t/lambda [[s CSeq] [u CSeq] [h (equiv s u)] [hp (Pos s)]]
        (pos-elim (val' s) (Pos u) hp
                  (fn [e he N1 hN1]
                    (let [e2 (q/mul q/half e)
                          he2 (t/app (qc "half_pos_of_pos") e he)
                          P #(q/lt (dist (at s %) (at u %)) e2)]
                      (eventually-elim P (Pos u) (t/app h e2 he2)
                                       (fn [N2 hN2]
                                         (pos-intro (val' u) e2 (nat-add N1 N2) he2
                                                    (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                      (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                        (t/app (qc "close_lower") e (at s n) (at u n)
                                                               (t/app hN1 n hn1) (t/app hN2 n hn2))))))))))))
    ;; Pos respects Equiv, so it lifts to R through propext
    (define! "Positive" (t/arrow R t/prop)
      (t/lam "x" R
             (fn [x]
               (t/app (t/quot-lift-prop CSeq (c "Equiv")
                                        (t/lambda [[s CSeq]] (Pos s))
                                        (t/lambda [[s CSeq] [u CSeq] [h (equiv s u)]]
                                          (t/propext' (Pos s) (Pos u)
                                                      (t/iff-intro (Pos s) (Pos u)
                                                                   (t/lam "p" (Pos s) #(t/app (c "pos_congr") s u h %))
                                                                   (t/lam "p" (Pos u)
                                                                          #(t/app (c "pos_congr") u s
                                                                                  (t/app (c "equiv_symm") s u h) %))))))
                      x))))
    (define! "lt" (t/arrow R (t/arrow R t/prop)) (t/lambda [[x R] [y R]] (positive (sub y x))))
    (define! "le" (t/arrow R (t/arrow R t/prop))
      (t/lambda [[x R] [y R]] (t/or' (lt x y) (k/eq-at R l1 x y))))
    ;; sums of eventually-positive sequences are eventually positive
    (theorem! "pos_add"
      (t/forall [[s CSeq] [u CSeq]] (implies (Pos s) (Pos u) (Pos (t/app (c "cadd") s u))))
      (t/lambda [[s CSeq] [u CSeq] [hs (Pos s)] [hu (Pos u)]]
        (let [goal (Pos (t/app (c "cadd") s u))]
          (pos-elim (val' s) goal hs
                    (fn [e1 he1 N1 hN1]
                      (pos-elim (val' u) goal hu
                                (fn [e2 he2 N2 hN2]
                                  (pos-intro (val' (t/app (c "cadd") s u)) (q/add e1 e2) (nat-add N1 N2)
                                             (t/app (qc "add_pos") e1 e2 he1 he2)
                                             (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                               (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                 (t/app (qc "add_lt_add") e1 (at s n) e2 (at u n)
                                                        (t/app hN1 n hn1) (t/app hN2 n hn2))))))))))))))

(defn- install-order-laws! []
    ;; laws on R by induction on representatives
    (r-law! "sub_add_sub" 3 #(add (sub %1 %2) (sub %2 %3)) #(sub %1 %3)
            #(cadd (cadd %1 (cneg %2)) (cadd %2 (cneg %3))) #(cadd %1 (cneg %3))
            (fn [x y z n] (t/app (qc "sub_add_sub") (at x n) (at y n) (at z n))))
    (r-law! "add_sub_add_left" 3 #(sub (add %1 %2) (add %1 %3)) #(sub %2 %3)
            #(cadd (cadd %1 %2) (cneg (cadd %1 %3))) #(cadd %2 (cneg %3))
            (fn [x y z n] (t/app (qc "add_sub_add_left") (at x n) (at y n) (at z n))))
    (theorem! "ofQ_sub"
      (t/forall [[p Q] [u Q]] (eq-r (sub (of-q p) (of-q u)) (of-q (q/sub p u))))
      (t/lambda [[p Q] [u Q]]
        (let [a (cadd (cconst p) (cneg (cconst u))) b (cconst (q/sub p u))]
          (t/quot-sound CSeq (c "Equiv") a b
                        (t/app (c "equiv_of_eq") a b
                               (t/lam "n" Nat (fn [_] (t/app (k/const "Eq.refl" l1) Q (q/sub p u)))))))))
    ;; positivity transfers along equalities and adds
    (theorem! "positive_add"
      (t/forall [[x R] [y R]] (implies (positive x) (positive y) (positive (add x y))))
      (q/lams ["x" "y"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (implies (positive (first ys)) (positive (second ys))
                                                     (positive (add (first ys) (second ys)))))
                                 (fn [[s u]] (t/app (c "pos_add") s u))))))
    (theorem! "not_positive_zero" (t/not' (positive zero))
      (t/lam "h" (positive zero)
             (fn [h]
               (pos-elim (val' (cconst q/zero)) t/false-prop h
                         (fn [e he N hN]
                           (t/app (qc "lt_irrefl") q/zero
                                  (t/app (qc "lt_trans") q/zero e q/zero he
                                         (t/app hN N (t/app (k/const "Nat.le_refl") N)))))))))
    (theorem! "lt_irrefl" (t/forall [[x R]] (t/not' (lt x x)))
      (t/lambda [[x R] [h (lt x x)]]
        (t/app (c "not_positive_zero")
               (t/transport-at R l1 (t/lambda [[z R]] (positive z)) (sub x x) zero
                               (t/app (c "sub_self") x) h))))
    (theorem! "lt_trans"
      (t/forall [[x R] [y R] [z R]] (implies (lt x y) (lt y z) (lt x z)))
      (t/lambda [[x R] [y R] [z R] [h1 (lt x y)] [h2 (lt y z)]]
        (t/transport-at R l1 (t/lambda [[w R]] (positive w)) (add (sub z y) (sub y x)) (sub z x)
                        (t/app (c "sub_add_sub") z y x)
                        (t/app (c "positive_add") (sub z y) (sub y x) h2 h1))))
    (theorem! "add_lt_add_left"
      (t/forall [[x R] [y R] [z R]] (implies (lt x y) (lt (add z x) (add z y))))
      (t/lambda [[x R] [y R] [z R] [h (lt x y)]]
        (t/transport-at R l1 (t/lambda [[w R]] (positive w)) (sub y x) (sub (add z y) (add z x))
                        (t/app (k/const "Eq.symm" l1) R (sub (add z y) (add z x)) (sub y x)
                               (t/app (c "add_sub_add_left") z y x))
                        h)))
    (theorem! "le_refl" (t/forall [[x R]] (le x x))
      (t/lambda [[x R]] (t/or-inr (lt x x) (eq-r x x) (t/app (k/const "Eq.refl" l1) R x))))
    (theorem! "le_of_lt" (t/forall [[x R] [y R]] (implies (lt x y) (le x y)))
      (t/lambda [[x R] [y R] [h (lt x y)]] (t/or-inl (lt x y) (eq-r x y) h)))
    ;; ofQ is an order embedding
    (theorem! "positive_ofQ"
      (t/forall [[p Q]] (implies (q/lt q/zero p) (positive (of-q p))))
      (t/lambda [[p Q] [h (q/lt q/zero p)]]
        (pos-intro (val' (cconst p)) (q/mul q/half p) (e/lit-nat 0)
                   (t/app (qc "half_pos_of_pos") p h)
                   (t/lambda [[n Nat] [_hn (nat-le (e/lit-nat 0) n)]]
                     (t/app (qc "half_lt_self") p h)))))
    (theorem! "ofQ_lt"
      (t/forall [[p Q] [u Q]] (implies (q/lt p u) (lt (of-q p) (of-q u))))
      (t/lambda [[p Q] [u Q] [h (q/lt p u)]]
        (t/transport-at R l1 (t/lambda [[z R]] (positive z)) (of-q (q/sub u p)) (sub (of-q u) (of-q p))
                        (t/app (k/const "Eq.symm" l1) R (sub (of-q u) (of-q p)) (of-q (q/sub u p))
                               (t/app (c "ofQ_sub") u p))
                        (t/app (c "positive_ofQ") (q/sub u p) (t/app (qc "sub_pos_of_lt") p u h)))))
    (theorem! "lt_ofQ"
      (t/forall [[p Q] [u Q]] (implies (lt (of-q p) (of-q u)) (q/lt p u)))
      (t/lambda [[p Q] [u Q] [h (lt (of-q p) (of-q u))]]
        (let [hp (t/transport-at R l1 (t/lambda [[z R]] (positive z)) (sub (of-q u) (of-q p)) (of-q (q/sub u p))
                                 (t/app (c "ofQ_sub") u p) h)]
          (t/app (qc "lt_of_sub_pos") p u
                 (pos-elim (val' (cconst (q/sub u p))) (q/lt q/zero (q/sub u p)) hp
                           (fn [e he N hN]
                             (t/app (qc "lt_trans") q/zero e (q/sub u p) he
                                    (t/app hN N (t/app (k/const "Nat.le_refl") N))))))))))

;; ## Apartness from zero
;;
;; A Cauchy sequence that is not equivalent to the zero sequence is eventually
;; bounded away from zero. This is the one classical step in the construction
;; (`Classical.byCases`); it is what an inverse and trichotomy rest on.

(defn- by-cases
  "Proof of `goal` from `pos-case : p → goal` and `neg-case : ¬p → goal`."
  [p goal pos-case neg-case]
  (t/app (k/const "Classical.byCases") p goal pos-case neg-case))

(defn- apart-body
  "`∃ δ, 0 < δ ∧ ∃ N, ∀ n ≥ N, δ < |s n|`."
  [f]
  (t/exists' Q (t/lambda [[d Q]]
                 (t/and' (pos d)
                         (t/exists' Nat (t/lambda [[N Nat]]
                                          (t/forall [[n Nat]]
                                            (t/arrow (nat-le N n) (q/lt d (q/abs (t/app f n)))))))))))

(defn- install-apart! []
  (let [czero (cconst q/zero)
        tail (fn [f d] (t/exists' Nat (t/lambda [[N Nat]]
                                        (t/forall [[n Nat]]
                                          (t/arrow (nat-le N n) (q/lt d (q/abs (t/app f n))))))))
        apart-intro (fn [f d N hp hall]
                      (t/exists-intro Q (t/lambda [[d' Q]] (t/and' (pos d') (tail f d'))) d
                                      (t/and-intro (pos d) (tail f d) hp
                                                   (t/exists-intro Nat
                                                                   (t/lambda [[M Nat]]
                                                                     (t/forall [[n Nat]]
                                                                       (t/arrow (nat-le M n) (q/lt d (q/abs (t/app f n))))))
                                                                   N hall))))]
    (define! "Apart" (t/arrow CSeq t/prop) (t/lambda [[s CSeq]] (apart-body (val' s))))
    (theorem! "apart_of_ne"
      (t/forall [[s CSeq]] (implies (t/not' (equiv s czero)) (t/app (c "Apart") s)))
      (t/lambda [[s CSeq] [hne (t/not' (equiv s czero))]]
        (let [f (val' s)
              A (apart-body f)]
          (by-cases A A
                    (t/lam "h" A identity)
                    ;; if s is nowhere bounded away from zero it converges to zero
                    (t/lam "hnA" (t/not' A)
                           (fn [hnA]
                             (t/false-elim A
                                    (t/app hne
                                           (t/lambda [[eps Q] [he (pos eps)]]
                                             (let [e2 (q/mul q/half eps)
                                                   he2 (t/app (qc "half_pos_of_pos") eps he)
                                                   P #(q/lt (dist (at s %) (at czero %)) eps)]
                                               (cauchy-elim f e2 (eventually P) (t/app (cauchy-of s) e2 he2)
                                                            (fn [N hN]
                                                              (eventually-intro P N
                                                                                (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                                                  (let [an (q/abs (t/app f n))
                                                                                        goal (q/lt (dist (at s n) (at czero n)) eps)
                                                                                        ;; |s n − 0| = |s n|
                                                                                        shift (fn [prf]
                                                                                                (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt (q/abs z) eps))
                                                                                                                (t/app f n) (q/sub (t/app f n) q/zero)
                                                                                                                (t/app (k/const "Eq.symm" l1) Q
                                                                                                                       (q/sub (t/app f n) q/zero) (t/app f n)
                                                                                                                       (t/app (qc "sub_zero") (t/app f n)))
                                                                                                                prf))]
                                                                    (by-cases (q/le eps an) goal
                                                                              ;; ε ≤ |s n| makes ε/2 a lower bound past N
                                                                              (t/lam "hge" (q/le eps an)
                                                                                     (fn [hge]
                                                                                       (t/false-elim goal
                                                                                              (t/app hnA
                                                                                                     (apart-intro f e2 N he2
                                                                                                                  (t/lambda [[m Nat] [hm (nat-le N m)]]
                                                                                                                    (t/app (qc "half_lt_abs") eps (t/app f n) (t/app f m)
                                                                                                                           hge (t/app hN n m hn hm))))))))
                                                                              (t/lam "hlt" (t/not' (q/le eps an))
                                                                                     #(shift (t/app (qc "lt_of_not_le") an eps %)))))))))))))))))))))

;; ## Trichotomy
;;
;; An apart sequence keeps a constant sign past the Cauchy threshold, so it is
;; eventually positive or eventually negative; on `R` that is trichotomy.

(defn- install-trichotomy! []
  (let [Pos #(t/app (c "Pos") %)
        cneg' #(t/app (c "cneg") %)]
    (theorem! "pos_or_neg_of_apart"
      (t/forall [[s CSeq]] (implies (t/app (c "Apart") s) (t/or' (Pos s) (Pos (cneg' s)))))
      (t/lambda [[s CSeq] [ha (t/app (c "Apart") s)]]
        (let [f (val' s)
              goal (t/or' (Pos s) (Pos (cneg' s)))
              tail (fn [d] (t/exists' Nat (t/lambda [[N Nat]]
                                            (t/forall [[n Nat]]
                                              (t/arrow (nat-le N n) (q/lt d (q/abs (t/app f n))))))))
              body (fn [d] (t/and' (pos d) (tail d)))]
          (t/exists-elim Q (t/lambda [[d Q]] (body d)) goal ha
                         (t/lambda [[d Q] [hd (body d)]]
                           (let [hdpos (t/and-left (pos d) (tail d) hd)]
                             (t/exists-elim Nat (t/lambda [[N Nat]]
                                                  (t/forall [[n Nat]]
                                                    (t/arrow (nat-le N n) (q/lt d (q/abs (t/app f n))))))
                                            goal (t/and-right (pos d) (tail d) hd)
                                            (t/lambda [[N1 Nat] [hN1 (t/forall [[n Nat]]
                                                                       (t/arrow (nat-le N1 n) (q/lt d (q/abs (t/app f n)))))]]
                                              (cauchy-elim f d goal (t/app (cauchy-of s) d hdpos)
                                                           (fn [N2 hN2]
                                                             (let [n0 (nat-add N1 N2)
                                                                   [h01 h02] (threshold-le N1 N2 n0 (t/app (k/const "Nat.le_refl") n0))
                                                                   x0 (t/app f n0)
                                                                   habs (t/app hN1 n0 h01)
                                                                   E (k/eq-at Q l1 x0 q/zero)]
                                                               ;; the sign of s at the threshold decides the sign of the tail
                                                               (t/or-elim (q/lt x0 q/zero) (t/or' E (q/lt q/zero x0)) goal
                                                                          (t/app (qc "lt_trichotomy") x0 q/zero)
                                                                          ;; negative: −s is eventually above (−s n₀) − δ
                                                                          (t/lam "hneg" (q/lt x0 q/zero)
                                                                                 (fn [hneg]
                                                                                   (let [y0 (q/neg x0)
                                                                                         hy0 (t/app (qc "neg_pos_of_neg") x0 hneg)
                                                                                         hd0 (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt d z)) (q/abs x0) y0
                                                                                                             (t/app (k/const "Eq.symm" l1) Q y0 (q/abs x0)
                                                                                                                    (t/app (k/const "Eq.trans" l1) Q y0 (q/abs y0) (q/abs x0)
                                                                                                                           (t/app (k/const "Eq.symm" l1) Q (q/abs y0) y0
                                                                                                                                  (t/app (qc "abs_of_pos") y0 hy0))
                                                                                                                           (t/app (qc "abs_neg") x0)))
                                                                                                             habs)]
                                                                                     (t/or-inr (Pos s) (Pos (cneg' s))
                                                                                               (pos-intro (val' (cneg' s)) (q/sub y0 d) n0
                                                                                                          (t/app (qc "sub_pos_of_lt") d y0 hd0)
                                                                                                          (t/lambda [[n Nat] [hn (nat-le n0 n)]]
                                                                                                            (let [[_hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                                              (t/app (qc "sub_lt_of_dist_lt") y0 (q/neg (t/app f n)) d
                                                                                                                     (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt z d))
                                                                                                                                     (q/abs (q/sub x0 (t/app f n)))
                                                                                                                                     (q/abs (q/sub y0 (q/neg (t/app f n))))
                                                                                                                                     (t/app (k/const "Eq.symm" l1) Q
                                                                                                                                            (q/abs (q/sub y0 (q/neg (t/app f n))))
                                                                                                                                            (q/abs (q/sub x0 (t/app f n)))
                                                                                                                                            (t/app (qc "dist_neg") x0 (t/app f n)))
                                                                                                                                     (t/app hN2 n0 n h02 hn2))))))))))
                                                                          (t/lam "hrest" (t/or' E (q/lt q/zero x0))
                                                                                 (fn [hrest]
                                                                                   (t/or-elim E (q/lt q/zero x0) goal hrest
                                                                                              ;; zero at the threshold contradicts δ < |s n₀|
                                                                                              (t/lam "he" E
                                                                                                     (fn [he]
                                                                                                       (t/false-elim goal
                                                                                                                     (t/app (qc "lt_irrefl") q/zero
                                                                                                                            (t/app (qc "lt_trans") q/zero d q/zero hdpos
                                                                                                                                   (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt d z))
                                                                                                                                                   (q/abs x0) q/zero
                                                                                                                                                   (t/app (k/const "Eq.trans" l1) Q (q/abs x0) (q/abs q/zero) q/zero
                                                                                                                                                          (t/app (k/const "congrArg" l1 l1) Q Q x0 q/zero (qc "abs") he)
                                                                                                                                                          (qc "abs_zero"))
                                                                                                                                                   habs))))))
                                                                                              ;; positive: s is eventually above s n₀ − δ
                                                                                              (t/lam "hpos" (q/lt q/zero x0)
                                                                                                     (fn [hpos]
                                                                                                       (let [hd0 (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt d z)) (q/abs x0) x0
                                                                                                                                 (t/app (qc "abs_of_pos") x0 hpos) habs)]
                                                                                                         (t/or-inl (Pos s) (Pos (cneg' s))
                                                                                                                   (pos-intro f (q/sub x0 d) n0
                                                                                                                              (t/app (qc "sub_pos_of_lt") d x0 hd0)
                                                                                                                              (t/lambda [[n Nat] [hn (nat-le n0 n)]]
                                                                                                                                (let [[_hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                                                                  (t/app (qc "sub_lt_of_dist_lt") x0 (t/app f n) d
                                                                                                                                         (t/app hN2 n0 n h02 hn2))))))))))))))))))))))))
    ;; R-level consequences
    (r-law! "neg_sub" 2 #(neg (sub %1 %2)) #(sub %2 %1)
            #(cneg (cadd %1 (cneg %2))) #(cadd %2 (cneg %1))
            (fn [x y n] (t/app (qc "neg_sub") (at x n) (at y n))))
    (r-law! "sub_add_cancel" 2 #(add (sub %1 %2) %2) (fn [x _] x)
            #(cadd (cadd %1 (cneg %2)) %2) (fn [x _] x)
            (fn [x y n] (t/app (qc "sub_add_cancel") (at x n) (at y n))))
    (theorem! "eq_of_sub_eq_zero"
      (t/forall [[x R] [y R]] (implies (eq-r (sub y x) zero) (eq-r x y)))
      (t/lambda [[x R] [y R] [h (eq-r (sub y x) zero)]]
        ;; y = (y − x) + x = 0 + x = x
        (let [step1 (t/app (k/const "congrArg" l1 l1) R R (sub y x) zero (t/lambda [[z R]] (add z x)) h)
              step2 (t/app (c "sub_add_cancel") y x)
              step3 (t/app (c "zero_add") x)]
          (t/app (k/const "Eq.symm" l1) R y x
                 (t/app (k/const "Eq.trans" l1) R y (add zero x) x
                        (t/app (k/const "Eq.trans" l1) R y (add (sub y x) x) (add zero x)
                               (t/app (k/const "Eq.symm" l1) R (add (sub y x) x) y step2)
                               step1)
                        step3)))))
    (theorem! "lt_trichotomy"
      (t/forall [[x R] [y R]] (t/or' (lt x y) (t/or' (eq-r x y) (lt y x))))
      (q/lams ["x" "y"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (let [[x y] ys] (t/or' (lt x y) (t/or' (eq-r x y) (lt y x)))))
                                 (fn [[a b]]
                                   (let [x (t/quot-mk CSeq (c "Equiv") a) y (t/quot-mk CSeq (c "Equiv") b)
                                         goal (t/or' (lt x y) (t/or' (eq-r x y) (lt y x)))
                                         dseq (cadd b (cneg a))
                                         czero (cconst q/zero)]
                                     (by-cases (equiv dseq czero) goal
                                               ;; y − x ≈ 0 makes x and y equal
                                               (t/lam "he" (equiv dseq czero)
                                                      (fn [he]
                                                        (t/or-inr (lt x y) (t/or' (eq-r x y) (lt y x))
                                                                  (t/or-inl (eq-r x y) (lt y x)
                                                                            (t/app (c "eq_of_sub_eq_zero") x y
                                                                                   (t/quot-sound CSeq (c "Equiv") dseq czero he))))))
                                               (t/lam "hne" (t/not' (equiv dseq czero))
                                                      (fn [hne]
                                                        (t/or-elim (Pos dseq) (Pos (cneg' dseq)) goal
                                                                   (t/app (c "pos_or_neg_of_apart") dseq
                                                                          (t/app (c "apart_of_ne") dseq hne))
                                                                   (t/lam "hp" (Pos dseq)
                                                                          #(t/or-inl (lt x y) (t/or' (eq-r x y) (lt y x)) %))
                                                                   (t/lam "hn" (Pos (cneg' dseq))
                                                                          (fn [hn]
                                                                            (t/or-inr (lt x y) (t/or' (eq-r x y) (lt y x))
                                                                                      (t/or-inr (eq-r x y) (lt y x)
                                                                                                (t/transport-at R l1 (t/lambda [[z R]] (positive z))
                                                                                                                (neg (sub y x)) (sub x y)
                                                                                                                (t/app (c "neg_sub") y x) hn)))))))))))))))))

;; ## The Archimedean property

(defn of-int [m] (t/app (c "ofInt") m))

(defn- install-archimedean! []
  (define! "ofInt" (t/arrow k/int-type R) (t/lambda [[m k/int-type]] (of-q (q/of-int m))))
  (theorem! "archimedean"
    (t/forall [[x R]] (t/exists' k/int-type (t/lambda [[m k/int-type]] (lt x (of-int m)))))
    (q/lams ["x"] R
            (fn [xs]
              (t/quot-ind-all* qconf xs
                               (fn [& ys] (t/exists' k/int-type (t/lambda [[m k/int-type]] (lt (first ys) (of-int m)))))
                               (fn [[s]]
                                 (let [x (t/quot-mk CSeq (c "Equiv") s)
                                       goal (t/exists' k/int-type (t/lambda [[m k/int-type]] (lt x (of-int m))))
                                       f (val' s)]
                                   ;; |s n| < B for all n, and B < m for some integer m
                                   (with-bound f (cauchy-of s) goal
                                     (fn [B _hB bs]
                                       (t/exists-elim k/int-type (t/lambda [[m k/int-type]] (q/lt B (q/of-int m))) goal
                                                      (t/app (qc "archimedean") B)
                                                      (t/lambda [[m k/int-type] [hm (q/lt B (q/of-int m))]]
                                                        (let [cm (q/of-int m)]
                                                          (t/exists-intro k/int-type
                                                                          (t/lambda [[m' k/int-type]] (lt x (of-int m'))) m
                                                                          (pos-intro (val' (cadd (cconst cm) (cneg s)))
                                                                                     (q/sub cm B) (e/lit-nat 0)
                                                                                     (t/app (qc "sub_pos_of_lt") B cm hm)
                                                                                     (t/lambda [[n Nat] [_hn (nat-le (e/lit-nat 0) n)]]
                                                                                       (t/app (qc "sub_lt_sub_left") (t/app f n) B cm
                                                                                              (t/app (qc "lt_of_le_of_lt") (t/app f n) (q/abs (t/app f n)) B
                                                                                                     (t/app (qc "le_abs") (t/app f n))
                                                                                                     (bs n)))))))))))))))))
  (r-law! "sub_zero" 1 #(sub % zero) identity #(cadd % (cneg (cconst q/zero))) identity
          (fn [x n] (t/app (qc "sub_zero") (at x n))))
  (theorem! "zero_lt_ofQ" (t/forall [[p Q]] (implies (q/lt q/zero p) (lt zero (of-q p))))
    (t/lambda [[p Q] [h (q/lt q/zero p)]]
      (t/transport-at R l1 (t/lambda [[z R]] (positive z)) (of-q p) (sub (of-q p) zero)
                      (t/app (k/const "Eq.symm" l1) R (sub (of-q p) zero) (of-q p)
                             (t/app (c "sub_zero") (of-q p)))
                      (t/app (c "positive_ofQ") p h)))))

;; ## The multiplicative inverse
;;
;; `cinv` inverts a Cauchy sequence pointwise when it is apart from zero and is
;; zero otherwise (the choice is classical, through `Classical.propDecidable`).
;; Past the apartness threshold `|a⁻¹ − b⁻¹| = |a⁻¹|·(|b⁻¹|·|b − a|)` is small
;; (`Q.dist_inv_lt`), which makes the inverted sequence Cauchy.

(defn- apart-tail [f d]
  (t/exists' Nat (t/lambda [[N Nat]]
                   (t/forall [[n Nat]] (t/arrow (nat-le N n) (q/lt d (q/abs (t/app f n))))))))

(defn- apart-all [f d N]
  (t/forall [[n Nat]] (t/arrow (nat-le N n) (q/lt d (q/abs (t/app f n))))))

(defn- apart-intro [f d N hp hall]
  (t/exists-intro Q (t/lambda [[d' Q]] (t/and' (pos d') (apart-tail f d'))) d
                  (t/and-intro (pos d) (apart-tail f d) hp
                               (t/exists-intro Nat (t/lambda [[M Nat]] (apart-all f d M)) N hall))))

(defn- apart-elim
  "Proof of `goal` from `h : Apart`, with `k` called on the bound `δ`, a proof
  of `0 < δ`, the threshold `N` and `hN : ∀ n ≥ N, δ < |f n|`."
  [f goal h k]
  (let [body (fn [d] (t/and' (pos d) (apart-tail f d)))]
    (t/exists-elim Q (t/lambda [[d Q]] (body d)) goal h
                   (t/lambda [[d Q] [hd (body d)]]
                     (t/exists-elim Nat (t/lambda [[N Nat]] (apart-all f d N)) goal
                                    (t/and-right (pos d) (apart-tail f d) hd)
                                    (t/lambda [[N Nat] [hN (apart-all f d N)]]
                                      (k d (t/and-left (pos d) (apart-tail f d) hd) N hN)))))))

(defn inv [x] (t/app (c "inv") x))

(defn- install-inv! []
  (let [Apart' #(t/app (c "Apart") %)
        inv-seq #(t/app (c "invSeq") %)
        czero (cconst q/zero)
        inst #(t/app (k/const "Classical.propDecidable") (Apart' %))
        pos-branch (fn [x] (t/lam "h" (Apart' x)
                                  #(make-cseq (inv-seq (val' x))
                                              (t/app (c "inv_cauchy") (val' x) (cauchy-of x) %))))
        neg-branch (fn [x] (t/lam "h" (t/not' (Apart' x)) (fn [_] czero)))
        branch-eq (fn [x yes? h]
                    (t/app (k/const (if yes? "dif_pos" "dif_neg") l1) (Apart' x) (inst x) h CSeq
                           (pos-branch x) (neg-branch x)))
        cinv #(t/app (c "cinv") %)
        symm-c (fn [x y e] (t/app (k/const "Eq.symm" l1) CSeq x y e))]
    (theorem! "apart_congr"
      (t/forall [[s CSeq] [u CSeq]] (implies (equiv s u) (Apart' s) (Apart' u)))
      (t/lambda [[s CSeq] [u CSeq] [h (equiv s u)] [ha (Apart' s)]]
        (apart-elim (val' s) (Apart' u) ha
                    (fn [d hd N1 hN1]
                      (let [d2 (q/mul q/half d)
                            hd2 (t/app (qc "half_pos_of_pos") d hd)
                            P #(q/lt (dist (at s %) (at u %)) d2)]
                        (eventually-elim P (Apart' u) (t/app h d2 hd2)
                                         (fn [N2 hN2]
                                           (apart-intro (val' u) d2 (nat-add N1 N2) hd2
                                                        (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                          (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                            (t/app (qc "half_lt_abs") d (at s n) (at u n)
                                                                   (t/app (qc "le_of_lt") d (q/abs (at s n))
                                                                          (t/app hN1 n hn1))
                                                                   (t/app hN2 n hn2))))))))))))
    (define! "invSeq" (t/arrow Seq Seq)
      (t/lambda [[f Seq]] (t/lam "n" Nat #(q/inv (t/app f %)))))
    (theorem! "inv_cauchy"
      (t/forall [[f Seq]] (implies (cauchy f) (apart-body f) (cauchy (inv-seq f))))
      (t/lambda [[f Seq] [hf (cauchy f)] [hap (apart-body f)] [eps Q] [he (pos eps)]]
        (let [h (inv-seq f)
              goal (t/exists' Nat (t/lambda [[N Nat]] (cauchy-body h eps N)))]
          (apart-elim f goal hap
                      (fn [d hd N0 hN0]
                        (let [tau (q/mul d (q/mul d eps))
                              htau (t/app (qc "mul_pos") d (q/mul d eps) hd
                                          (t/app (qc "mul_pos") d eps hd he))]
                          (cauchy-elim f tau goal (t/app hf tau htau)
                                       (fn [N1 hN1]
                                         (cauchy-intro h eps (nat-add N0 N1)
                                                       (t/lambda [[m Nat] [n Nat]
                                                                  [hm (nat-le (nat-add N0 N1) m)]
                                                                  [hn (nat-le (nat-add N0 N1) n)]]
                                                         (let [[hm0 hm1] (threshold-le N0 N1 m hm)
                                                               [hn0 hn1] (threshold-le N0 N1 n hn)]
                                                           (t/app (qc "dist_inv_lt") d (t/app f m) (t/app f n) eps
                                                                  hd (t/app hN0 m hm0) (t/app hN0 n hn0)
                                                                  (t/app hN1 m n hm1 hn1)))))))))))))
    (define! "cinv" (t/arrow CSeq CSeq)
      (t/lambda [[s CSeq]]
        (t/app (k/const "dite" l1) CSeq (Apart' s) (inst s) (pos-branch s) (neg-branch s))))
    (theorem! "inv_congr"
      (t/forall [[s CSeq] [u CSeq]] (implies (equiv s u) (equiv (cinv s) (cinv u))))
      (t/lambda [[s CSeq] [u CSeq] [heq (equiv s u)]]
        (let [goal (equiv (cinv s) (cinv u))
              cases (fn [x f-yes f-no]
                      (t/or-elim (Apart' x) (t/not' (Apart' x)) goal
                                 (t/decidable-em (Apart' x) (inst x))
                                 (t/lam "h" (Apart' x) f-yes)
                                 (t/lam "hn" (t/not' (Apart' x)) f-no)))
              ;; rewrite both inverses back to the branch values they reduce to
              through (fn [X Y ex ey prf]
                        (let [m1 (t/lambda [[z CSeq]] (equiv z (cinv u)))
                              m2 (t/lambda [[z CSeq]] (equiv X z))
                              step (t/transport-at CSeq l1 m2 Y (cinv u) (symm-c (cinv u) Y ey) prf)]
                          (t/transport-at CSeq l1 m1 X (cinv s) (symm-c (cinv s) X ex) step)))
              ;; both apart: δ/2 bounds both sequences below past the thresholds
              both (fn [hs _hu]
                     (t/lambda [[eps Q] [he (pos eps)]]
                       (let [P #(q/lt (dist (q/inv (at s %)) (q/inv (at u %))) eps)
                             g (eventually P)]
                         (apart-elim (val' s) g hs
                                     (fn [d hd N0 hN0]
                                       (let [d2 (q/mul q/half d)
                                             hd2 (t/app (qc "half_pos_of_pos") d hd)
                                             tau (q/mul d2 (q/mul d2 eps))
                                             htau (t/app (qc "mul_pos") d2 (q/mul d2 eps) hd2
                                                         (t/app (qc "mul_pos") d2 eps hd2 he))
                                             P1 #(q/lt (dist (at s %) (at u %)) d2)
                                             P2 #(q/lt (dist (at s %) (at u %)) tau)]
                                         (eventually-elim P1 g (t/app heq d2 hd2)
                                                          (fn [N1 hN1]
                                                            (eventually-elim P2 g (t/app heq tau htau)
                                                                             (fn [N2 hN2]
                                                                               (let [N12 (nat-add N1 N2)]
                                                                                 (eventually-intro P (nat-add N0 N12)
                                                                                                   (t/lambda [[n Nat] [hn (nat-le (nat-add N0 N12) n)]]
                                                                                                     (let [[hn0 hnr] (threshold-le N0 N12 n hn)
                                                                                                           [hn1 hn2] (threshold-le N1 N2 n hnr)
                                                                                                           hsn (t/app hN0 n hn0)
                                                                                                           hs2 (t/app (qc "lt_trans") d2 d (q/abs (at s n))
                                                                                                                      (t/app (qc "half_lt_self") d hd) hsn)
                                                                                                           hu2 (t/app (qc "half_lt_abs") d (at s n) (at u n)
                                                                                                                      (t/app (qc "le_of_lt") d (q/abs (at s n)) hsn)
                                                                                                                      (t/app hN1 n hn1))]
                                                                                                       (t/app (qc "dist_inv_lt") d2 (at s n) (at u n) eps
                                                                                                              hd2 hs2 hu2 (t/app hN2 n hn2))))))))))))))))]
          (cases s
                 (fn [hs]
                   (cases u
                          (fn [hu] (through (t/app (pos-branch s) hs) (t/app (pos-branch u) hu)
                                            (branch-eq s true hs) (branch-eq u true hu)
                                            (both hs hu)))
                          (fn [hnu] (t/absurd' (Apart' u) goal (t/app (c "apart_congr") s u heq hs) hnu))))
                 (fn [hns]
                   (cases u
                          (fn [hu] (t/absurd' (Apart' s) goal
                                              (t/app (c "apart_congr") u s (t/app (c "equiv_symm") s u heq) hu)
                                              hns))
                          (fn [hnu] (through (t/app (neg-branch s) hns) (t/app (neg-branch u) hnu)
                                             (branch-eq s false hns) (branch-eq u false hnu)
                                             (t/app (c "equiv_refl") czero)))))))))
    (define! "inv" (t/arrow R R)
      (t/lift1* qconf cinv (fn [a b h] (t/app (c "inv_congr") a b h))))
    ;; x·x⁻¹ = 1: past the apartness threshold every term is invertible
    (theorem! "mul_inv_cancel"
      (t/forall [[x R]] (implies (t/not' (eq-r x zero)) (eq-r (mul x (inv x)) one)))
      (q/lams ["x"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (let [x (first ys)]
                                              (implies (t/not' (eq-r x zero)) (eq-r (mul x (inv x)) one))))
                                 (fn [[s]]
                                   (let [x (t/quot-mk CSeq (c "Equiv") s)
                                         _goal (eq-r (mul x (inv x)) one)]
                                     (t/lam "hne" (t/not' (eq-r x zero))
                                            (fn [hne]
                                              (let [hnq (t/lam "he" (equiv s czero)
                                                               #(t/app hne (t/quot-sound CSeq (c "Equiv") s czero %)))
                                                    hap (t/app (c "apart_of_ne") s hnq)
                                                    inv-s (t/app (pos-branch s) hap)
                                                    ;; the product is eventually exactly 1
                                                    prf (t/lambda [[eps Q] [he (pos eps)]]
                                                          (let [P #(q/lt (dist (q/mul (at s %) (q/inv (at s %))) q/one) eps)]
                                                            (apart-elim (val' s) (eventually P) hap
                                                                        (fn [d hd N0 hN0]
                                                                          (eventually-intro P N0
                                                                                            (t/lambda [[n Nat] [hn (nat-le N0 n)]]
                                                                                              (t/transport-at Q l1
                                                                                                              (t/lambda [[z Q]] (q/lt (dist z q/one) eps))
                                                                                                              q/one (q/mul (at s n) (q/inv (at s n)))
                                                                                                              (t/app (k/const "Eq.symm" l1) Q
                                                                                                                     (q/mul (at s n) (q/inv (at s n))) q/one
                                                                                                                     (t/app (qc "mul_inv_cancel") (at s n)
                                                                                                                            (t/app (qc "ne_zero_of_lt_abs") d (at s n)
                                                                                                                                   hd (t/app hN0 n hn))))
                                                                                                              (dist-self-lt q/one eps he))))))))
                                                    sound-eq (t/quot-sound CSeq (c "Equiv")
                                                                           (t/app (c "cmul") s inv-s) (cconst q/one) prf)]
                                                ;; rewrite cinv s back into the product
                                                (t/transport-at CSeq l1
                                                                (t/lambda [[z CSeq]]
                                                                  (eq-r (t/quot-mk CSeq (c "Equiv") (t/app (c "cmul") s z)) one))
                                                                inv-s (cinv s)
                                                                (symm-c (cinv s) inv-s (branch-eq s true hap))
                                                                sound-eq))))))))))))

;; ## Density of ℚ in ℝ
;;
;; If `x < y` then `y − x` is eventually above some ε, and `s n₀ + ε/2` (for a
;; threshold index `n₀`) sits strictly between them, with ε/4 to spare on each
;; side.

(defn- install-density! []
  (let [quarter #(q/mul q/half (q/mul q/half %))]
    (theorem! "dense"
      (t/forall [[x R] [y R]]
        (implies (lt x y)
                 (t/exists' Q (t/lambda [[p Q]] (t/and' (lt x (of-q p)) (lt (of-q p) y))))))
      (q/lams ["x" "y"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys]
                                   (let [[x y] ys]
                                     (implies (lt x y)
                                              (t/exists' Q (t/lambda [[p Q]] (t/and' (lt x (of-q p)) (lt (of-q p) y)))))))
                                 (fn [[a b]]
                                   (let [x (t/quot-mk CSeq (c "Equiv") a) y (t/quot-mk CSeq (c "Equiv") b)
                                         between (fn [p] (t/and' (lt x (of-q p)) (lt (of-q p) y)))
                                         goal (t/exists' Q (t/lambda [[p Q]] (between p)))
                                         diff (cadd b (cneg a))]
                                     (t/lam "hlt" (lt x y)
                                            (fn [hlt]
                                              (pos-elim (val' diff) goal hlt
                                                        (fn [eps he N hN]
                                                          (let [r (quarter eps)
                                                                hr (t/app (qc "half_pos_of_pos") (q/mul q/half eps)
                                                                          (t/app (qc "half_pos_of_pos") eps he))]
                                                            (cauchy-elim (val' a) r goal (t/app (cauchy-of a) r hr)
                                                                         (fn [N1 hN1]
                                                                           (let [n0 (nat-add N N1)
                                                                                 [_hn0 hn1] (threshold-le N N1 n0 (t/app (k/const "Nat.le_refl") n0))
                                                                                 base (at a n0)
                                                                                 p (q/add base (q/mul q/half eps))]
                                                                             (t/exists-intro Q (t/lambda [[p' Q]] (between p')) p
                                                                                             (t/and-intro (lt x (of-q p)) (lt (of-q p) y)
                                                                                                          ;; x < p: p − a m > (a n₀ + ε/2) − (a n₀ + ε/4) = ε/4
                                                                                                          (pos-intro (val' (cadd (cconst p) (cneg a))) r n0 hr
                                                                                                                     (t/lambda [[m Nat] [hm (nat-le n0 m)]]
                                                                                                                       (let [[_hm0 hm1] (threshold-le N N1 m hm)]
                                                                                                                         (rewrite-lt-left
                                                                                                                          (q/sub (q/add base (q/mul q/half eps)) (q/add base r)) r
                                                                                                                          (q/sub p (at a m))
                                                                                                                          (t/app (qc "quarter_gap_left") base eps)
                                                                                                                          (t/app (qc "sub_lt_sub_left") (at a m) (q/add base r) p
                                                                                                                                 (t/app (qc "lt_add_of_abs_sub_lt") (at a m) base r
                                                                                                                                        (t/app hN1 m n0 hm1 hn1)))))))
                                                                                                          ;; p < y: b m − p > ((a n₀ − ε/4) + ε) − (a n₀ + ε/2) = ε/4
                                                                                                          (pos-intro (val' (cadd b (cneg (cconst p)))) r n0 hr
                                                                                                                     (t/lambda [[m Nat] [hm (nat-le n0 m)]]
                                                                                                                       (let [[hm0 hm1] (threshold-le N N1 m hm)
                                                                                                                             am (at a m) bm (at b m)
                                                                                                                             ;; ε + a m < b m
                                                                                                                             hA (rewrite-lt-right
                                                                                                                                 (q/add (q/sub bm am) am) bm (q/add eps am)
                                                                                                                                 (t/app (qc "sub_add_cancel") bm am)
                                                                                                                                 (t/app (qc "add_lt_add_right") eps (q/sub bm am) am
                                                                                                                                        (t/app hN m hm0)))
                                                                                                                             ;; (a n₀ − ε/4) + ε < ε + a m
                                                                                                                             hB (rewrite-lt-right
                                                                                                                                 (q/add am eps) (q/add eps am)
                                                                                                                                 (q/add (q/sub base r) eps)
                                                                                                                                 (t/app (qc "add_comm") am eps)
                                                                                                                                 (t/app (qc "add_lt_add_right") (q/sub base r) am eps
                                                                                                                                        (t/app (qc "sub_lt_of_dist_lt") base am r
                                                                                                                                               (t/app hN1 n0 m hn1 hm1))))
                                                                                                                             hC (t/app (qc "lt_trans") (q/add (q/sub base r) eps) (q/add eps am) bm hB hA)]
                                                                                                                         (rewrite-lt-left
                                                                                                                          (q/sub (q/add (q/sub base r) eps) p) r (q/sub bm p)
                                                                                                                          (t/app (qc "quarter_gap_right") base eps)
                                                                                                                          (t/app (qc "add_lt_add_right") (q/add (q/sub base r) eps) bm (q/neg p) hC)))))))))))))))))))))))

;; ## Absolute value and the estimates completeness needs

(defn abs [x] (t/app (c "abs") x))

(defn- cabs [s] (t/app (c "cabs") s))

(defn- install-abs! []
  (define! "absSeq" (t/arrow Seq Seq) (t/lambda [[f Seq]] (t/lam "n" Nat #(q/abs (t/app f %)))))
  (let [abs-seq #(t/app (c "absSeq") %)]
    (theorem! "abs_cauchy"
      (t/forall [[f Seq]] (implies (cauchy f) (cauchy (abs-seq f))))
      (t/lambda [[f Seq] [hf (cauchy f)] [eps Q] [he (pos eps)]]
        (let [h (abs-seq f)
              goal (t/exists' Nat (t/lambda [[N Nat]] (cauchy-body h eps N)))]
          (cauchy-elim f eps goal (t/app hf eps he)
                       (fn [N hN]
                         (cauchy-intro h eps N
                                       (t/lambda [[m Nat] [n Nat] [hm (nat-le N m)] [hn (nat-le N n)]]
                                         (t/app (qc "lt_of_le_of_lt")
                                                (dist (q/abs (t/app f m)) (q/abs (t/app f n)))
                                                (dist (t/app f m) (t/app f n)) eps
                                                (t/app (qc "abs_sub_abs_le") (t/app f m) (t/app f n))
                                                (t/app hN m n hm hn)))))))))
    (define! "cabs" (t/arrow CSeq CSeq)
      (t/lambda [[s CSeq]]
        (make-cseq (abs-seq (val' s)) (t/app (c "abs_cauchy") (val' s) (cauchy-of s)))))
    (theorem! "abs_congr_seq"
      (t/forall [[s CSeq] [u CSeq]] (implies (equiv s u) (equiv (cabs s) (cabs u))))
      (t/lambda [[s CSeq] [u CSeq] [h (equiv s u)] [eps Q] [he (pos eps)]]
        (let [P #(q/lt (dist (at s %) (at u %)) eps)
              P' #(q/lt (dist (q/abs (at s %)) (q/abs (at u %))) eps)]
          (eventually-elim P (eventually P') (t/app h eps he)
                           (fn [N hN]
                             (eventually-intro P' N
                                               (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                 (t/app (qc "lt_of_le_of_lt")
                                                        (dist (q/abs (at s n)) (q/abs (at u n)))
                                                        (dist (at s n) (at u n)) eps
                                                        (t/app (qc "abs_sub_abs_le") (at s n) (at u n))
                                                        (t/app hN n hn)))))))))
    (define! "abs" (t/arrow R R)
      (t/lift1* qconf cabs (fn [a b h] (t/app (c "abs_congr_seq") a b h))))
    ;; pointwise laws
    (r-law! "abs_sub_comm" 2 #(abs (sub %1 %2)) #(abs (sub %2 %1))
            #(cabs (cadd %1 (cneg %2))) #(cabs (cadd %2 (cneg %1)))
            (fn [x y n] (t/app (qc "abs_sub_comm") (at x n) (at y n))))
    (r-law! "sub_add_add" 4 #(sub (add %1 %2) (add %3 %4)) #(add (sub %1 %3) (sub %2 %4))
            #(cadd (cadd %1 %2) (cneg (cadd %3 %4))) #(cadd (cadd %1 (cneg %3)) (cadd %2 (cneg %4)))
            (fn [x y z w n] (t/app (qc "sub_add_add") (at x n) (at y n) (at z n) (at w n))))
    (theorem! "ofQ_abs"
      (t/forall [[p Q]] (eq-r (abs (of-q p)) (of-q (q/abs p))))
      (t/lambda [[p Q]]
        (let [a (cabs (cconst p)) b (cconst (q/abs p))]
          (t/quot-sound CSeq (c "Equiv") a b
                        (t/app (c "equiv_of_eq") a b
                               (t/lam "n" Nat (fn [_] (t/app (k/const "Eq.refl" l1) Q (q/abs p)))))))))
    (theorem! "add_lt_add"
      (t/forall [[x R] [a R] [y R] [b R]] (implies (lt x a) (lt y b) (lt (add x y) (add a b))))
      (t/lambda [[x R] [a R] [y R] [b R] [hx (lt x a)] [hy (lt y b)]]
        (t/transport-at R l1 (t/lambda [[z R]] (positive z))
                        (add (sub a x) (sub b y)) (sub (add a b) (add x y))
                        (t/app (k/const "Eq.symm" l1) R (sub (add a b) (add x y)) (add (sub a x) (sub b y))
                               (t/app (c "sub_add_add") a b x y))
                        (t/app (c "positive_add") (sub a x) (sub b y) hx hy))))
    ;; |x − z| < a + b from |x − y| < a and |y − z| < b
    (theorem! "dist_triangle_lt"
      (t/forall [[x R] [y R] [z R] [a R] [b R]]
        (implies (lt (abs (sub x y)) a) (lt (abs (sub y z)) b) (lt (abs (sub x z)) (add a b))))
      (q/lams ["x" "y" "z" "a" "b"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys]
                                   (let [[x y z a b] ys]
                                     (implies (lt (abs (sub x y)) a) (lt (abs (sub y z)) b)
                                              (lt (abs (sub x z)) (add a b)))))
                                 (fn [[sx sy sz sa sb]]
                                   (let [mk' #(t/quot-mk CSeq (c "Equiv") %)
                                         x (mk' sx) y (mk' sy) z (mk' sz) a (mk' sa) b (mk' sb)
                                         goal (lt (abs (sub x z)) (add a b))
                                         dx (cabs (cadd sx (cneg sy)))
                                         dy (cabs (cadd sy (cneg sz)))
                                         dz (cabs (cadd sx (cneg sz)))]
                                     (t/lam "h1" (lt (abs (sub x y)) a)
                                            (fn [h1]
                                              (t/lam "h2" (lt (abs (sub y z)) b)
                                                     (fn [h2]
                                                       (pos-elim (val' (cadd sa (cneg dx))) goal h1
                                                                 (fn [e1 he1 N1 hN1]
                                                                   (pos-elim (val' (cadd sb (cneg dy))) goal h2
                                                                             (fn [e2 he2 N2 hN2]
                                                                               (pos-intro (val' (cadd (cadd sa sb) (cneg dz)))
                                                                                          (q/add e1 e2) (nat-add N1 N2)
                                                                                          (t/app (qc "add_pos") e1 e2 he1 he2)
                                                                                          (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                                            (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                              (t/app (qc "triangle_gap") e1 e2
                                                                                                     (at sa n) (at sb n)
                                                                                                     (q/abs (q/sub (at sx n) (at sy n)))
                                                                                                     (q/abs (q/sub (at sy n) (at sz n)))
                                                                                                     (q/abs (q/sub (at sx n) (at sz n)))
                                                                                                     (t/app hN1 n hn1) (t/app hN2 n hn2)
                                                                                                     (t/app (qc "dist_triangle") (at sx n) (at sy n) (at sz n))))))))))))))))))))
    ;; a sequence eventually within e of a rational sits within 2e of it in R
    (theorem! "abs_sub_ofQ_lt"
      (t/forall [[s CSeq] [cq Q] [e Q] [N Nat]]
        (implies (pos e)
                 (t/forall [[m Nat]] (t/arrow (nat-le N m) (q/lt (dist (at s m) cq) e)))
                 (lt (abs (sub (t/quot-mk CSeq (c "Equiv") s) (of-q cq))) (of-q (q/add e e)))))
      (t/lambda [[s CSeq] [cq Q] [e Q] [N Nat] [he (pos e)]
                 [hall (t/forall [[m Nat]] (t/arrow (nat-le N m) (q/lt (dist (at s m) cq) e)))]]
        (pos-intro (val' (cadd (cconst (q/add e e)) (cneg (cabs (cadd s (cneg (cconst cq))))))) e N he
                   (t/lambda [[m Nat] [hm (nat-le N m)]]
                     (t/app (qc "lt_double_sub") (dist (at s m) cq) e (t/app hall m hm))))))
    ;; every real is within any positive rational of some rational
    (theorem! "approx"
      (t/forall [[x R] [d Q]]
        (implies (q/lt q/zero d) (t/exists' Q (t/lambda [[p Q]] (lt (abs (sub x (of-q p))) (of-q d))))))
      (q/lams ["x"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys]
                                   (let [x (first ys)]
                                     (t/forall [[d Q]]
                                       (implies (q/lt q/zero d)
                                                (t/exists' Q (t/lambda [[p Q]] (lt (abs (sub x (of-q p))) (of-q d))))))))
                                 (fn [[s]]
                                   (let [x (t/quot-mk CSeq (c "Equiv") s)]
                                     (t/lambda [[d Q] [hd (q/lt q/zero d)]]
                                       (let [e (q/mul q/half d)
                                             he (t/app (qc "half_pos_of_pos") d hd)
                                             goal (t/exists' Q (t/lambda [[p Q]] (lt (abs (sub x (of-q p))) (of-q d))))]
                                         (cauchy-elim (val' s) e goal (t/app (cauchy-of s) e he)
                                                      (fn [N hN]
                                                        (let [p (at s N)]
                                                          (t/exists-intro Q (t/lambda [[p' Q]] (lt (abs (sub x (of-q p'))) (of-q d))) p
                                                                          (t/transport-at R l1
                                                                                          (t/lambda [[z R]] (lt (abs (sub x (of-q p))) z))
                                                                                          (of-q (q/add e e)) (of-q d)
                                                                                          (t/app (k/const "congrArg" l1 l1) Q R (q/add e e) d
                                                                                                 (c "ofQ") (t/app (qc "half_add_half") d))
                                                                                          (t/app (c "abs_sub_ofQ_lt") s p e N he
                                                                                                 (t/lambda [[m Nat] [hm (nat-le N m)]]
                                                                                                   (t/app hN m N hm (t/app (k/const "Nat.le_refl") N)))))))))))))))))))

;; ## Completeness
;;
;; For each `n` pick a rational `g n` within `small n` of `X n`
;; (`Classical.choose` on `approx`). Then `g` is Cauchy in ℚ and its class is
;; the limit of `X`.

(defn- install-complete! []
  (theorem! "add_lt_add_right"
    (t/forall [[x R] [y R] [z R]] (implies (lt x y) (lt (add x z) (add y z))))
    (t/lambda [[x R] [y R] [z R] [h (lt x y)]]
      (let [h1 (t/app (c "add_lt_add_left") x y z h)
            h2 (t/transport-at R l1 (t/lambda [[w R]] (lt w (add z y))) (add z x) (add x z)
                               (t/app (c "add_comm") z x) h1)]
        (t/transport-at R l1 (t/lambda [[w R]] (lt (add x z) w)) (add z y) (add y z)
                        (t/app (c "add_comm") z y) h2))))
  (theorem! "sum3_ofQ"
    (t/forall [[a Q] [b Q] [cq Q]]
      (eq-r (add (add (of-q a) (of-q b)) (of-q cq)) (of-q (q/add (q/add a b) cq))))
    (t/lambda [[a Q] [b Q] [cq Q]]
      (let [x (cadd (cadd (cconst a) (cconst b)) (cconst cq))
            y (cconst (q/add (q/add a b) cq))]
        (t/quot-sound CSeq (c "Equiv") x y
                      (t/app (c "equiv_of_eq") x y
                             (t/lam "n" Nat (fn [_] (t/app (k/const "Eq.refl" l1) Q (q/add (q/add a b) cq)))))))))
  (let [RSeq (t/arrow Nat R)
        quarter #(q/mul q/half (q/mul q/half %))
        approx-prop (fn [X n p] (lt (abs (sub (t/app X n) (of-q p))) (of-q (q/small n))))
        pred (fn [X n] (t/lambda [[p Q]] (approx-prop X n p)))
        hex (fn [X n] (t/app (c "approx") (t/app X n) (q/small n) (t/app (qc "small_pos") n)))
        choose (fn [X n] (t/app (k/const "Classical.choose" l1) Q (pred X n) (hex X n)))
        spec (fn [X n] (t/app (k/const "Classical.choose_spec" l1) Q (pred X n) (hex X n)))
        gseq (fn [X] (t/lam "n" Nat #(choose X %)))
        cauchyR #(t/app (c "CauchyR") %)
        ;; small m < e for every m past the threshold of small_lt
        small-below (fn [N0 hN0 e m hm]
                      (t/app (qc "lt_of_le_of_lt") (q/small m) (q/small N0) e
                             (t/app (qc "small_mono") N0 m hm) hN0))]
    (define! "CauchyR" (t/arrow RSeq t/prop)
      (t/lambda [[X RSeq]]
        (t/forall [[eps R]]
          (t/arrow (lt zero eps)
                   (t/exists' Nat (t/lambda [[N Nat]]
                                    (t/forall [[m Nat] [n Nat]]
                                      (implies (nat-le N m) (nat-le N n)
                                               (lt (abs (sub (t/app X m) (t/app X n))) eps)))))))))
    (define! "TendsTo" (t/arrow RSeq (t/arrow R t/prop))
      (t/lambda [[X RSeq] [L R]]
        (t/forall [[eps R]]
          (t/arrow (lt zero eps)
                   (t/exists' Nat (t/lambda [[N Nat]]
                                    (t/forall [[n Nat]]
                                      (t/arrow (nat-le N n) (lt (abs (sub (t/app X n) L)) eps)))))))))
    ;; the chosen rationals form a Cauchy sequence: |g m − g n| ≤ small m + ε/2 + small n
    (theorem! "approx_cauchy"
      (t/forall [[X RSeq]] (implies (cauchyR X) (cauchy (gseq X))))
      (t/lambda [[X RSeq] [hX (cauchyR X)] [eps Q] [he (pos eps)]]
        (let [g (gseq X)
              q2 (q/mul q/half eps) q4 (quarter eps)
              hq2 (t/app (qc "half_pos_of_pos") eps he)
              hq4 (t/app (qc "half_pos_of_pos") q2 hq2)
              E (of-q q2)
              goal (t/exists' Nat (t/lambda [[N Nat]] (cauchy-body g eps N)))
              xbody (fn [N] (t/forall [[m Nat] [n Nat]]
                              (implies (nat-le N m) (nat-le N n)
                                       (lt (abs (sub (t/app X m) (t/app X n))) E))))]
          (t/exists-elim Nat (t/lambda [[N Nat]] (q/lt (q/small N) q4)) goal
                         (t/app (qc "small_lt") q4 hq4)
                         (t/lambda [[N0 Nat] [hN0 (q/lt (q/small N0) q4)]]
                           (t/exists-elim Nat (t/lambda [[N Nat]] (xbody N)) goal
                                          (t/app hX E (t/app (c "zero_lt_ofQ") q2 hq2))
                                          (t/lambda [[N1 Nat] [hN1 (xbody N1)]]
                                            (cauchy-intro g eps (nat-add N0 N1)
                                                          (t/lambda [[m Nat] [n Nat]
                                                                     [hm (nat-le (nat-add N0 N1) m)]
                                                                     [hn (nat-le (nat-add N0 N1) n)]]
                                                            (let [[hm0 hm1] (threshold-le N0 N1 m hm)
                                                                  [hn0 hn1] (threshold-le N0 N1 n hn)
                                                                  gm (of-q (choose X m)) gn (of-q (choose X n))
                                                                  sm (of-q (q/small m)) sn (of-q (q/small n))
                                                                  ;; |ofQ (g m) − X m| < ofQ (small m)
                                                                  A (t/transport-at R l1 (t/lambda [[z R]] (lt z sm))
                                                                                    (abs (sub (t/app X m) gm)) (abs (sub gm (t/app X m)))
                                                                                    (t/app (c "abs_sub_comm") (t/app X m) gm)
                                                                                    (spec X m))
                                                                  t1 (t/app (c "dist_triangle_lt") gm (t/app X m) (t/app X n) sm E
                                                                            A (t/app hN1 m n hm1 hn1))
                                                                  t2 (t/app (c "dist_triangle_lt") gm (t/app X n) gn (add sm E) sn
                                                                            t1 (spec X n))
                                                                  ;; (small m + ε/2) + small n < (ε/4 + ε/2) + ε/4 = ε
                                                                  b1 (t/app (c "add_lt_add_right") (add sm E) (add (of-q q4) E) sn
                                                                            (t/app (c "add_lt_add_right") sm (of-q q4) E
                                                                                   (t/app (c "ofQ_lt") (q/small m) q4 (small-below N0 hN0 q4 m hm0))))
                                                                  b2 (t/app (c "add_lt_add_left") sn (of-q q4) (add (of-q q4) E)
                                                                            (t/app (c "ofQ_lt") (q/small n) q4 (small-below N0 hN0 q4 n hn0)))
                                                                  bound (t/app (c "lt_trans") (abs (sub gm gn)) (add (add sm E) sn)
                                                                               (add (add (of-q q4) E) (of-q q4))
                                                                               t2 (t/app (c "lt_trans") (add (add sm E) sn)
                                                                                         (add (add (of-q q4) E) sn)
                                                                                         (add (add (of-q q4) E) (of-q q4))
                                                                                         b1 b2))
                                                                  ;; rewrite the bound to ofQ ε and descend to Q
                                                                  as-ofQ (t/transport-at R l1 (t/lambda [[z R]] (lt (abs (sub gm gn)) z))
                                                                                         (add (add (of-q q4) E) (of-q q4)) (of-q eps)
                                                                                         (t/app (k/const "Eq.trans" l1) R
                                                                                                (add (add (of-q q4) E) (of-q q4))
                                                                                                (of-q (q/add (q/add q4 q2) q4)) (of-q eps)
                                                                                                (t/app (c "sum3_ofQ") q4 q2 q4)
                                                                                                (t/app (k/const "congrArg" l1 l1) Q R
                                                                                                       (q/add (q/add q4 q2) q4) eps (c "ofQ")
                                                                                                       (t/app (qc "quarter_half_quarter") eps)))
                                                                                         bound)
                                                                  as-q (t/transport-at R l1 (t/lambda [[z R]] (lt z (of-q eps)))
                                                                                       (abs (sub gm gn)) (of-q (dist (choose X m) (choose X n)))
                                                                                       (t/app (k/const "Eq.trans" l1) R
                                                                                              (abs (sub gm gn)) (abs (of-q (q/sub (choose X m) (choose X n))))
                                                                                              (of-q (dist (choose X m) (choose X n)))
                                                                                              (t/app (k/const "congrArg" l1 l1) R R
                                                                                                     (sub gm gn) (of-q (q/sub (choose X m) (choose X n)))
                                                                                                     (c "abs") (t/app (c "ofQ_sub") (choose X m) (choose X n)))
                                                                                              (t/app (c "ofQ_abs") (q/sub (choose X m) (choose X n))))
                                                                                       as-ofQ)]
                                                              (t/app (c "lt_ofQ") (dist (t/app g m) (t/app g n)) eps as-q)))))))))))
    (theorem! "complete"
      (t/forall [[X RSeq]]
        (implies (cauchyR X) (t/exists' R (t/lambda [[L R]] (t/app (c "TendsTo") X L)))))
      (t/lambda [[X RSeq] [hX (cauchyR X)]]
        (let [g (gseq X)
              gc (make-cseq g (t/app (c "approx_cauchy") X hX))
              L (t/quot-mk CSeq (c "Equiv") gc)
              _goal (t/exists' R (t/lambda [[L' R]] (t/app (c "TendsTo") X L')))]
          (t/exists-intro R (t/lambda [[L' R]] (t/app (c "TendsTo") X L')) L
                          (t/lambda [[eps R] [hpos (lt zero eps)]]
                            (let [tgoal (t/exists' Nat (t/lambda [[N Nat]]
                                                         (t/forall [[n Nat]]
                                                           (t/arrow (nat-le N n) (lt (abs (sub (t/app X n) L)) eps)))))
                                  between (fn [p] (t/and' (lt zero (of-q p)) (lt (of-q p) eps)))]
                              ;; a rational 0 < p with ofQ p < ε
                              (t/exists-elim Q (t/lambda [[p Q]] (between p)) tgoal
                                             (t/app (c "dense") zero eps hpos)
                                             (t/lambda [[p Q] [hp (between p)]]
                                               (let [hp0 (t/app (c "lt_ofQ") q/zero p (t/and-left (lt zero (of-q p)) (lt (of-q p) eps) hp))
                                                     hpe (t/and-right (lt zero (of-q p)) (lt (of-q p) eps) hp)
                                                     p2 (q/mul q/half p) p4 (quarter p)
                                                     hp2 (t/app (qc "half_pos_of_pos") p hp0)
                                                     hp4 (t/app (qc "half_pos_of_pos") p2 hp2)
]
                                                 ;; N2: g is Cauchy at p/4;  N3: small below p/2
                                                 (cauchy-elim g p4 tgoal (t/app (t/app (c "approx_cauchy") X hX) p4 hp4)
                                                              (fn [N2 hN2]
                                                                (t/exists-elim Nat (t/lambda [[N Nat]] (q/lt (q/small N) p2)) tgoal
                                                                               (t/app (qc "small_lt") p2 hp2)
                                                                               (t/lambda [[N3 Nat] [hN3 (q/lt (q/small N3) p2)]]
                                                                                 (t/exists-intro Nat
                                                                                                 (t/lambda [[N Nat]]
                                                                                                   (t/forall [[n Nat]]
                                                                                                     (t/arrow (nat-le N n) (lt (abs (sub (t/app X n) L)) eps))))
                                                                                                 (nat-add N2 N3)
                                                                                                 (t/lambda [[n Nat] [hn (nat-le (nat-add N2 N3) n)]]
                                                                                                   (let [[hn2 hn3] (threshold-le N2 N3 n hn)
                                                                                                         gn (of-q (choose X n))
                                                                                                         sn (of-q (q/small n))
                                                                                                         ;; |ofQ (g n) − L| < ofQ (p/2)
                                                                                                         tail (t/transport-at R l1
                                                                                                                              (t/lambda [[z R]] (lt (abs (sub gn L)) z))
                                                                                                                              (of-q (q/add p4 p4)) (of-q p2)
                                                                                                                              (t/app (k/const "congrArg" l1 l1) Q R
                                                                                                                                     (q/add p4 p4) p2 (c "ofQ")
                                                                                                                                     (t/app (qc "quarter_add_quarter") p))
                                                                                                                              (t/transport-at R l1
                                                                                                                                              (t/lambda [[z R]] (lt z (of-q (q/add p4 p4))))
                                                                                                                                              (abs (sub L gn)) (abs (sub gn L))
                                                                                                                                              (t/app (c "abs_sub_comm") L gn)
                                                                                                                                              (t/app (c "abs_sub_ofQ_lt") gc (choose X n) p4 N2 hp4
                                                                                                                                                     (t/lambda [[m Nat] [hm (nat-le N2 m)]]
                                                                                                                                                       (t/app hN2 m n hm hn2)))))
                                                                                                         tri (t/app (c "dist_triangle_lt") (t/app X n) gn L sn (of-q p2)
                                                                                                                    (spec X n) tail)
                                                                                                         ;; small n + p/2 < p/2 + p/2 = p < ε
                                                                                                         b (t/app (c "add_lt_add_right") sn (of-q p2) (of-q p2)
                                                                                                                  (t/app (c "ofQ_lt") (q/small n) p2 (small-below N3 hN3 p2 n hn3)))
                                                                                                         bound (t/app (c "lt_trans") (abs (sub (t/app X n) L))
                                                                                                                      (add sn (of-q p2)) (add (of-q p2) (of-q p2)) tri b)
                                                                                                         as-p (t/transport-at R l1
                                                                                                                              (t/lambda [[z R]] (lt (abs (sub (t/app X n) L)) z))
                                                                                                                              (add (of-q p2) (of-q p2)) (of-q p)
                                                                                                                              (t/app (k/const "Eq.trans" l1) R
                                                                                                                                     (add (of-q p2) (of-q p2)) (of-q (q/add p2 p2)) (of-q p)
                                                                                                                                     (t/app (c "ofQ_add") p2 p2)
                                                                                                                                     (t/app (k/const "congrArg" l1 l1) Q R (q/add p2 p2) p
                                                                                                                                            (c "ofQ") (t/app (qc "half_add_half") p)))
                                                                                                                              bound)]
                                                                                                     (t/app (c "lt_trans") (abs (sub (t/app X n) L)) (of-q p) eps
                                                                                                            as-p hpe)))))))))))))))))))

;; ## Order toolkit on ℝ
;;
;; `0 < x` unfolds to `Positive (x − 0)`, so the bridges `Pos_of_lt_zero` and
;; `lt_zero_of_Pos` absorb that shift once and the rest of the file works with
;; `Pos` on representatives.

(defn- apart-of [s] (t/app (c "Apart") s))
(defn- inv-inst [s] (t/app (k/const "Classical.propDecidable") (apart-of s)))
(defn- inv-pos-branch [s]
  (t/lam "h" (apart-of s)
         #(make-cseq (t/app (c "invSeq") (val' s))
                     (t/app (c "inv_cauchy") (val' s) (cauchy-of s) %))))
(defn- inv-neg-branch [s] (t/lam "h" (t/not' (apart-of s)) (fn [_] (cconst q/zero))))
(defn- inv-branch-eq [s h]
  (t/app (k/const "dif_pos" l1) (apart-of s) (inv-inst s) h CSeq
         (inv-pos-branch s) (inv-neg-branch s)))

(def half (c "half"))

(defn- install-order-toolkit! []
  (let [mk' #(t/quot-mk CSeq (c "Equiv") %)
        czero (cconst q/zero)
        Pos #(t/app (c "Pos") %)
        symm-r (fn [x y e] (t/app (k/const "Eq.symm" l1) R x y e))
        step (fn [x y e] {:lhs x :rhs y :type R :level l1 :term e})
        chain (fn [& maps] (:term (apply k/trans maps)))]
    (theorem! "equiv_of_eventually_eq"
      (t/forall [[s CSeq] [u CSeq] [N Nat]]
        (implies (t/forall [[n Nat]] (t/arrow (nat-le N n) (k/eq-at Q l1 (at s n) (at u n))))
                 (equiv s u)))
      (t/lambda [[s CSeq] [u CSeq] [N Nat]
                 [h (t/forall [[n Nat]] (t/arrow (nat-le N n) (k/eq-at Q l1 (at s n) (at u n))))]
                 [eps Q] [he (pos eps)]]
        (eventually-intro #(q/lt (dist (at s %) (at u %)) eps) N
                          (t/lambda [[n Nat] [hn (nat-le N n)]]
                            (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt (dist (at s n) z) eps))
                                            (at s n) (at u n) (t/app h n hn)
                                            (dist-self-lt (at s n) eps he))))))
    (theorem! "lt_zero_of_Pos"
      (t/forall [[s CSeq]] (implies (Pos s) (lt zero (mk' s))))
      (t/lambda [[s CSeq] [h (Pos s)]]
        (pos-elim (val' s) (lt zero (mk' s)) h
                  (fn [e he N hN]
                    (pos-intro (val' (cadd s (cneg czero))) e N he
                               (t/lambda [[n Nat] [hn (nat-le N n)]]
                                 (rewrite-lt-right (at s n) (q/sub (at s n) q/zero) e
                                                   (t/app (k/const "Eq.symm" l1) Q
                                                          (q/sub (at s n) q/zero) (at s n)
                                                          (t/app (qc "sub_zero") (at s n)))
                                                   (t/app hN n hn))))))))
    (theorem! "Pos_of_lt_zero"
      (t/forall [[s CSeq]] (implies (lt zero (mk' s)) (Pos s)))
      (t/lambda [[s CSeq] [h (lt zero (mk' s))]]
        (pos-elim (val' (cadd s (cneg czero))) (Pos s) h
                  (fn [e he N hN]
                    (pos-intro (val' s) e N he
                               (t/lambda [[n Nat] [hn (nat-le N n)]]
                                 (rewrite-lt-right (q/sub (at s n) q/zero) (at s n) e
                                                   (t/app (qc "sub_zero") (at s n))
                                                   (t/app hN n hn))))))))
    (theorem! "positive_of_lt_zero"
      (t/forall [[x R]] (implies (lt zero x) (positive x)))
      (q/lams ["x"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (implies (lt zero (first ys)) (positive (first ys))))
                                 (fn [[a]] (t/app (c "Pos_of_lt_zero") a))))))
    (theorem! "lt_zero_of_positive"
      (t/forall [[x R]] (implies (positive x) (lt zero x)))
      (q/lams ["x"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (implies (positive (first ys)) (lt zero (first ys))))
                                 (fn [[a]] (t/app (c "lt_zero_of_Pos") a))))))
    (theorem! "ne_of_lt"
      (t/forall [[x R] [y R]] (implies (lt x y) (t/not' (eq-r x y))))
      (t/lambda [[x R] [y R] [h (lt x y)] [e (eq-r x y)]]
        (t/app (c "lt_irrefl") x
               (t/transport-at R l1 (t/lambda [[z R]] (lt x z)) y x (symm-r x y e) h))))
    (theorem! "pos_apart"
      (t/forall [[s CSeq]] (implies (Pos s) (apart-of s)))
      (t/lambda [[s CSeq] [h (Pos s)]]
        (pos-elim (val' s) (apart-of s) h
                  (fn [e he N hN]
                    (apart-intro (val' s) e N he
                                 (t/lambda [[n Nat] [hn (nat-le N n)]]
                                   (t/app (qc "lt_of_lt_of_le") e (at s n) (q/abs (at s n))
                                          (t/app hN n hn) (t/app (qc "le_abs") (at s n)))))))))
    (theorem! "abs_pos_of_ne"
      (t/forall [[x R] [y R]] (implies (t/not' (eq-r x y)) (lt zero (abs (sub x y)))))
      (q/lams ["x" "y"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (let [[x y] ys]
                                              (implies (t/not' (eq-r x y)) (lt zero (abs (sub x y))))))
                                 (fn [[a b]]
                                   (let [x (mk' a) y (mk' b) d (cadd a (cneg b))]
                                     (t/lam "hne" (t/not' (eq-r x y))
                                            (fn [hne]
                                              (let [hnq (t/lam "he" (equiv d czero)
                                                               (fn [he]
                                                                 (t/app hne
                                                                        (symm-r y x
                                                                                (t/app (c "eq_of_sub_eq_zero") y x
                                                                                       (t/quot-sound CSeq (c "Equiv") d czero he))))))
                                                    hap (t/app (c "apart_of_ne") d hnq)]
                                                (t/app (c "lt_zero_of_Pos") (cabs d)
                                                       (apart-elim (val' d) (Pos (cabs d)) hap
                                                                   (fn [dd hd N hN]
                                                                     (pos-intro (val' (cabs d)) dd N hd
                                                                                (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                                                  (t/app hN n hn)))))))))))))))
    (theorem! "abs_of_pos"
      (t/forall [[x R]] (implies (lt zero x) (eq-r (abs x) x)))
      (q/lams ["x"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (implies (lt zero (first ys)) (eq-r (abs (first ys)) (first ys))))
                                 (fn [[a]]
                                   (t/lam "h" (lt zero (mk' a))
                                          (fn [h]
                                            (pos-elim (val' a) (eq-r (abs (mk' a)) (mk' a))
                                                      (t/app (c "Pos_of_lt_zero") a h)
                                                      (fn [e he N hN]
                                                        (t/quot-sound CSeq (c "Equiv") (cabs a) a
                                                                      (t/app (c "equiv_of_eventually_eq") (cabs a) a N
                                                                             (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                                               (t/app (qc "abs_of_pos") (at a n)
                                                                                      (t/app (qc "lt_trans") q/zero e (at a n)
                                                                                             he (t/app hN n hn)))))))))))))))
    (theorem! "mul_pos"
      (t/forall [[x R] [y R]] (implies (lt zero x) (lt zero y) (lt zero (mul x y))))
      (q/lams ["x" "y"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (let [[x y] ys] (implies (lt zero x) (lt zero y) (lt zero (mul x y)))))
                                 (fn [[a b]]
                                   (t/lam "hx" (lt zero (mk' a))
                                          (fn [hx]
                                            (t/lam "hy" (lt zero (mk' b))
                                                   (fn [hy]
                                                     (t/app (c "lt_zero_of_Pos") (cmul a b)
                                                            (pos-elim (val' a) (Pos (cmul a b)) (t/app (c "Pos_of_lt_zero") a hx)
                                                                      (fn [e1 he1 N1 hN1]
                                                                        (pos-elim (val' b) (Pos (cmul a b)) (t/app (c "Pos_of_lt_zero") b hy)
                                                                                  (fn [e2 he2 N2 hN2]
                                                                                    (pos-intro (val' (cmul a b)) (q/mul e1 e2) (nat-add N1 N2)
                                                                                               (t/app (qc "mul_pos") e1 e2 he1 he2)
                                                                                               (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                                                 (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                                   (t/app (qc "mul_lt_of_lt_of_lt") e1 (at a n) e2 (at b n)
                                                                                                          (t/app (qc "le_of_lt") q/zero e1 he1)
                                                                                                          (t/app hN1 n hn1)
                                                                                                          (t/app (qc "le_of_lt") q/zero e2 he2)
                                                                                                          (t/app hN2 n hn2)))))))))))))))))))
    ;; halving
    (define! "half" R (of-q q/half))
    (theorem! "half_pos"
      (t/forall [[x R]] (implies (lt zero x) (lt zero (mul half x))))
      (t/lambda [[x R] [h (lt zero x)]]
        (t/app (c "mul_pos") half x (t/app (c "zero_lt_ofQ") q/half (qc "half_pos")) h)))
    (r-law! "half_add_half" 1 #(add (mul half %) (mul half %)) identity
            #(cadd (cmul (cconst q/half) %) (cmul (cconst q/half) %)) identity
            (fn [x n] (t/app (qc "half_add_half") (at x n))))
    (r-law! "sub_half" 1 #(sub % (mul half %)) #(mul half %)
            #(cadd % (cneg (cmul (cconst q/half) %))) #(cmul (cconst q/half) %)
            (fn [x n] (t/app (qc "sub_half") (at x n))))
    (theorem! "half_lt_self"
      (t/forall [[x R]] (implies (lt zero x) (lt (mul half x) x)))
      (t/lambda [[x R] [h (lt zero x)]]
        (t/transport-at R l1 (t/lambda [[z R]] (positive z)) (mul half x) (sub x (mul half x))
                        (symm-r (sub x (mul half x)) (mul half x) (t/app (c "sub_half") x))
                        (t/app (c "positive_of_lt_zero") (mul half x) (t/app (c "half_pos") x h)))))
    ;; strict estimates lifted pointwise
    (theorem! "dist_add_lt"
      (t/forall [[a R] [s R] [b R] [u R] [A R] [B R]]
        (implies (lt (abs (sub a s)) A) (lt (abs (sub b u)) B)
                 (lt (abs (sub (add a b) (add s u))) (add A B))))
      (q/lams ["a" "s" "b" "u" "A" "B"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys]
                                   (let [[a s b u A B] ys]
                                     (implies (lt (abs (sub a s)) A) (lt (abs (sub b u)) B)
                                              (lt (abs (sub (add a b) (add s u))) (add A B)))))
                                 (fn [[sa ss sb su sA sB]]
                                   (let [d1 (cabs (cadd sa (cneg ss)))
                                         d2 (cabs (cadd sb (cneg su)))
                                         d3 (cabs (cadd (cadd sa sb) (cneg (cadd ss su))))
                                         goal (lt (abs (sub (add (mk' sa) (mk' sb)) (add (mk' ss) (mk' su))))
                                                  (add (mk' sA) (mk' sB)))]
                                     (t/lam "h1" (lt (abs (sub (mk' sa) (mk' ss))) (mk' sA))
                                            (fn [h1]
                                              (t/lam "h2" (lt (abs (sub (mk' sb) (mk' su))) (mk' sB))
                                                     (fn [h2]
                                                       (pos-elim (val' (cadd sA (cneg d1))) goal h1
                                                                 (fn [e1 he1 N1 hN1]
                                                                   (pos-elim (val' (cadd sB (cneg d2))) goal h2
                                                                             (fn [e2 he2 N2 hN2]
                                                                               (pos-intro (val' (cadd (cadd sA sB) (cneg d3)))
                                                                                          (q/add e1 e2) (nat-add N1 N2)
                                                                                          (t/app (qc "add_pos") e1 e2 he1 he2)
                                                                                          (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                                            (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                              (t/app (qc "triangle_gap") e1 e2
                                                                                                     (at sA n) (at sB n)
                                                                                                     (q/abs (q/sub (at sa n) (at ss n)))
                                                                                                     (q/abs (q/sub (at sb n) (at su n)))
                                                                                                     (q/abs (q/sub (q/add (at sa n) (at sb n))
                                                                                                                   (q/add (at ss n) (at su n))))
                                                                                                     (t/app hN1 n hn1) (t/app hN2 n hn2)
                                                                                                     (t/app (qc "dist_add_le") (at sa n) (at sb n)
                                                                                                            (at ss n) (at su n))))))))))))))))))))
    (theorem! "abs_mul_lt"
      (t/forall [[u R] [v R] [A R] [B R]]
        (implies (lt (abs u) A) (lt (abs v) B) (lt (abs (mul u v)) (mul A B))))
      (q/lams ["u" "v" "A" "B"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys]
                                   (let [[u v A B] ys]
                                     (implies (lt (abs u) A) (lt (abs v) B) (lt (abs (mul u v)) (mul A B)))))
                                 (fn [[su sv sA sB]]
                                   (let [goal (lt (abs (mul (mk' su) (mk' sv))) (mul (mk' sA) (mk' sB)))]
                                     (t/lam "h1" (lt (abs (mk' su)) (mk' sA))
                                            (fn [h1]
                                              (t/lam "h2" (lt (abs (mk' sv)) (mk' sB))
                                                     (fn [h2]
                                                       (pos-elim (val' (cadd sA (cneg (cabs su)))) goal h1
                                                                 (fn [e1 he1 N1 hN1]
                                                                   (pos-elim (val' (cadd sB (cneg (cabs sv)))) goal h2
                                                                             (fn [e2 he2 N2 hN2]
                                                                               (pos-intro (val' (cadd (cmul sA sB) (cneg (cabs (cmul su sv)))))
                                                                                          (q/mul e1 e2) (nat-add N1 N2)
                                                                                          (t/app (qc "mul_pos") e1 e2 he1 he2)
                                                                                          (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                                            (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                              (t/app (qc "mul_gap") e1 e2 (at sA n) (at sB n)
                                                                                                     (at su n) (at sv n) he1 he2
                                                                                                     (t/app hN1 n hn1) (t/app hN2 n hn2)))))))))))))))))))
    (theorem! "abs_lt_add"
      (t/forall [[a R] [b R] [E R]]
        (implies (lt (abs (sub b a)) E) (lt (abs b) (add (abs a) E))))
      (q/lams ["a" "b" "E"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys]
                                   (let [[a b E] ys] (implies (lt (abs (sub b a)) E) (lt (abs b) (add (abs a) E)))))
                                 (fn [[sa sb sE]]
                                   (let [goal (lt (abs (mk' sb)) (add (abs (mk' sa)) (mk' sE)))]
                                     (t/lam "h" (lt (abs (sub (mk' sb) (mk' sa))) (mk' sE))
                                            (fn [h]
                                              (pos-elim (val' (cadd sE (cneg (cabs (cadd sb (cneg sa)))))) goal h
                                                        (fn [e he N hN]
                                                          (pos-intro (val' (cadd (cadd (cabs sa) sE) (cneg (cabs sb)))) e N he
                                                                     (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                                       (t/app (qc "abs_gap") e (at sa n) (at sb n) (at sE n)
                                                                              (t/app hN n hn))))))))))))))
    (theorem! "abs_add_one_pos"
      (t/forall [[x R]] (lt zero (add (abs x) one)))
      (q/lams ["x"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (lt zero (add (abs (first ys)) one)))
                                 (fn [[a]]
                                   (pos-intro (val' (cadd (cadd (cabs a) (cconst q/one)) (cneg czero)))
                                              q/half (e/lit-nat 0) (qc "half_pos")
                                              (t/lambda [[n Nat] [_hn (nat-le (e/lit-nat 0) n)]]
                                                (rewrite-lt-right (q/add (q/abs (at a n)) q/one)
                                                                  (q/sub (q/add (q/abs (at a n)) q/one) q/zero)
                                                                  q/half
                                                                  (t/app (k/const "Eq.symm" l1) Q
                                                                         (q/sub (q/add (q/abs (at a n)) q/one) q/zero)
                                                                         (q/add (q/abs (at a n)) q/one)
                                                                         (t/app (qc "sub_zero") (q/add (q/abs (at a n)) q/one)))
                                                                  (t/app (qc "half_lt_abs_add_one") (at a n))))))))))
    ;; inverses of positives are positive: 1/B is a lower bound past the threshold
    (theorem! "inv_pos"
      (t/forall [[x R]] (implies (lt zero x) (lt zero (inv x))))
      (q/lams ["x"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys] (implies (lt zero (first ys)) (lt zero (inv (first ys)))))
                                 (fn [[a]]
                                   (t/lam "h" (lt zero (mk' a))
                                          (fn [h]
                                            (let [hp (t/app (c "Pos_of_lt_zero") a h)
                                                  hap (t/app (c "pos_apart") a hp)
                                                  X (t/app (inv-pos-branch a) hap)
                                                  _goal (lt zero (mk' (t/app (c "cinv") a)))]
                                              (t/transport-at CSeq l1 (t/lambda [[z CSeq]] (lt zero (mk' z)))
                                                              X (t/app (c "cinv") a)
                                                              (t/app (k/const "Eq.symm" l1) CSeq
                                                                     (t/app (c "cinv") a) X (inv-branch-eq a hap))
                                                              (t/app (c "lt_zero_of_Pos") X
                                                                     (pos-elim (val' a) (Pos X) hp
                                                                               (fn [e he N hN]
                                                                                 (with-bound (val' a) (cauchy-of a) (Pos X)
                                                                                   (fn [B hB bs]
                                                                                     (pos-intro (val' X) (q/inv B) N
                                                                                                (t/app (qc "inv_pos") B hB)
                                                                                                (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                                                                  (let [an (at a n)
                                                                                                        h0 (t/app (qc "lt_trans") q/zero e an he (t/app hN n hn))
                                                                                                        hB' (t/app (qc "lt_of_le_of_lt") an (q/abs an) B
                                                                                                                   (t/app (qc "le_abs") an) (bs n))]
                                                                                                    (t/app (qc "inv_lt_inv_of_lt") an B h0 hB'))))))))))))))))))
    ;; field arithmetic used to build tolerances
    (doseq [[label arg] [["mul_congr_fst" :fst] ["mul_congr_snd" :snd]]]
      (theorem! label
        (t/forall [[a R] [x R] [y R]]
          (implies (eq-r x y)
                   (if (= arg :fst) (eq-r (mul x a) (mul y a)) (eq-r (mul a x) (mul a y)))))
        (t/lambda [[a R] [x R] [y R] [h (eq-r x y)]]
          (t/app (k/const "congrArg" l1 l1) R R x y
                 (if (= arg :fst) (t/lambda [[z R]] (mul z a)) (t/lambda [[z R]] (mul a z))) h))))
    (theorem! "mul_inv_mul"
      (t/forall [[a R] [e R]] (implies (lt zero a) (eq-r (mul a (mul (inv a) e)) e)))
      (t/lambda [[a R] [e R] [h (lt zero a)]]
        (let [ia (inv a)
              a-ne (t/lam "h0" (eq-r a zero)
                          #(t/app (c "ne_of_lt") zero a h (symm-r a zero %)))]
          (chain (step (mul a (mul ia e)) (mul (mul a ia) e)
                       (symm-r (mul (mul a ia) e) (mul a (mul ia e)) (t/app (c "mul_assoc") a ia e)))
                 (step (mul (mul a ia) e) (mul one e)
                       (t/app (c "mul_congr_fst") e (mul a ia) one (t/app (c "mul_inv_cancel") a a-ne)))
                 (step (mul one e) e (t/app (c "one_mul") e))))))
    ;; a positive number below two given positives
    (theorem! "exists_pos_lt_both"
      (t/forall [[a R] [b R]]
        (implies (lt zero a) (lt zero b)
                 (t/exists' R (t/lambda [[cc R]] (t/and' (lt zero cc) (t/and' (lt cc a) (lt cc b)))))))
      (t/lambda [[a R] [b R] [ha (lt zero a)] [hb (lt zero b)]]
        (let [body (fn [cc] (t/and' (lt zero cc) (t/and' (lt cc a) (lt cc b))))
              goal (t/exists' R (t/lambda [[cc R]] (body cc)))
              pick (fn [w hw hwa hwb]
                     (t/exists-intro R (t/lambda [[cc R]] (body cc)) w
                                     (t/and-intro (lt zero w) (t/and' (lt w a) (lt w b)) hw
                                                  (t/and-intro (lt w a) (lt w b) hwa hwb))))
              ha2 (t/app (c "half_pos") a ha) hb2 (t/app (c "half_pos") b hb)
              hsa (t/app (c "half_lt_self") a ha) hsb (t/app (c "half_lt_self") b hb)]
          (t/or-elim (lt a b) (t/or' (eq-r a b) (lt b a)) goal
                     (t/app (c "lt_trichotomy") a b)
                     (t/lam "hab" (lt a b)
                            (fn [hab]
                              (pick (mul half a) ha2 hsa
                                    (t/app (c "lt_trans") (mul half a) a b hsa hab))))
                     (t/lam "hrest" (t/or' (eq-r a b) (lt b a))
                            (fn [hrest]
                              (t/or-elim (eq-r a b) (lt b a) goal hrest
                                         (t/lam "he" (eq-r a b)
                                                (fn [he]
                                                  (pick (mul half a) ha2 hsa
                                                        (t/transport-at R l1 (t/lambda [[z R]] (lt (mul half a) z)) a b he hsa))))
                                         (t/lam "hba" (lt b a)
                                                (fn [hba]
                                                  (pick (mul half b) hb2
                                                        (t/app (c "lt_trans") (mul half b) b a hsb hba)
                                                        hsb))))))))))))

;; ## Limits and continuity (M4)
;;
;; `TendsToAt f x L := ∀ ε > 0, ∃ δ > 0, ∀ y, 0 < |y − x| → |y − x| < δ →
;; |f y − L| < ε`, the punctured ε-δ limit, and `ContinuousAt` in its
;; unpunctured form.

(def ^:private Fn (t/arrow R R))

(defn tends-to-at [f x L] (t/app (c "TendsToAt") f x L))
(defn continuous-at [f x] (t/app (c "ContinuousAt") f x))
(defn continuous [f] (t/app (c "Continuous") f))

(defn- install-limit-lemmas! []
  (let [symm-r (fn [x y e] (t/app (k/const "Eq.symm" l1) R x y e))]
    (r-law! "abs_zero" 0 (fn [] (abs zero)) (fn [] zero)
            (fn [] (cabs (cconst q/zero))) (fn [] (cconst q/zero))
            (fn [_n] (qc "abs_zero")))
    (r-law! "abs_mul" 2 #(abs (mul %1 %2)) #(mul (abs %1) (abs %2))
            #(cabs (cmul %1 %2)) #(cmul (cabs %1) (cabs %2))
            (fn [x y n] (t/app (qc "abs_mul") (at x n) (at y n))))
    (theorem! "zero_lt_one" (lt zero one)
      (t/app (c "zero_lt_ofQ") q/one (qc "zero_lt_one")))
    (r-law! "abs_sub_self" 1 #(abs (sub % %)) (constantly zero)
            #(cabs (cadd % (cneg %))) (constantly (cconst q/zero))
            (fn [x n]
              (t/app (k/const "Eq.trans" l1) Q (q/abs (q/sub (at x n) (at x n))) (q/abs q/zero) q/zero
                     (t/app (qc "abs_congr") (q/sub (at x n) (at x n)) q/zero
                            (t/app (qc "sub_self") (at x n)))
                     (qc "abs_zero"))))
    (r-law! "dist_neg" 2 #(abs (sub (neg %1) (neg %2))) #(abs (sub %1 %2))
            #(cabs (cadd (cneg %1) (cneg (cneg %2)))) #(cabs (cadd %1 (cneg %2)))
            (fn [x y n] (t/app (qc "dist_neg") (at x n) (at y n))))
    (r-law! "mul_sub_decomp" 4 #(sub (mul %1 %2) (mul %3 %4))
            #(add (mul (sub %1 %3) %2) (mul %3 (sub %2 %4)))
            #(cadd (cmul %1 %2) (cneg (cmul %3 %4)))
            #(cadd (cmul (cadd %1 (cneg %3)) %2) (cmul %3 (cadd %2 (cneg %4))))
            (fn [x y z w n] (t/app (qc "mul_sub_decomp") (at x n) (at y n) (at z n) (at w n))))
    (r-law! "add_sub_cancel_left" 2 #(sub (add %1 %2) %1) (fn [_ y] y)
            #(cadd (cadd %1 %2) (cneg %1)) (fn [_ b] b)
            (fn [x y n] (t/app (qc "add_sub_cancel_left") (at x n) (at y n))))
    (theorem! "abs_lt_abs_add_one"
      (t/forall [[x R]] (lt (abs x) (add (abs x) one)))
      (t/lambda [[x R]]
        (t/transport-at R l1 (t/lambda [[z R]] (positive z)) one (sub (add (abs x) one) (abs x))
                        (symm-r (sub (add (abs x) one) (abs x)) one
                                (t/app (c "add_sub_cancel_left") (abs x) one))
                        (t/app (c "positive_of_lt_zero") one (c "zero_lt_one")))))
    ;; |a + b| < A + B from |a| < A and |b| < B
    (theorem! "abs_add_lt"
      (t/forall [[a R] [b R] [A R] [B R]]
        (implies (lt (abs a) A) (lt (abs b) B) (lt (abs (add a b)) (add A B))))
      (q/lams ["a" "b" "A" "B"] R
              (fn [xs]
                (t/quot-ind-all* qconf xs
                                 (fn [& ys]
                                   (let [[a b A B] ys]
                                     (implies (lt (abs a) A) (lt (abs b) B) (lt (abs (add a b)) (add A B)))))
                                 (fn [[sa sb sA sB]]
                                   (let [mk' #(t/quot-mk CSeq (c "Equiv") %)
                                         goal (lt (abs (add (mk' sa) (mk' sb))) (add (mk' sA) (mk' sB)))]
                                     (t/lam "h1" (lt (abs (mk' sa)) (mk' sA))
                                            (fn [h1]
                                              (t/lam "h2" (lt (abs (mk' sb)) (mk' sB))
                                                     (fn [h2]
                                                       (pos-elim (val' (cadd sA (cneg (cabs sa)))) goal h1
                                                                 (fn [e1 he1 N1 hN1]
                                                                   (pos-elim (val' (cadd sB (cneg (cabs sb)))) goal h2
                                                                             (fn [e2 he2 N2 hN2]
                                                                               (pos-intro (val' (cadd (cadd sA sB) (cneg (cabs (cadd sa sb)))))
                                                                                          (q/add e1 e2) (nat-add N1 N2)
                                                                                          (t/app (qc "add_pos") e1 e2 he1 he2)
                                                                                          (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                                            (let [[hn1 hn2] (threshold-le N1 N2 n hn)]
                                                                                              (t/app (qc "triangle_gap") e1 e2 (at sA n) (at sB n)
                                                                                                     (q/abs (at sa n)) (q/abs (at sb n))
                                                                                                     (q/abs (q/add (at sa n) (at sb n)))
                                                                                                     (t/app hN1 n hn1) (t/app hN2 n hn2)
                                                                                                     (t/app (qc "abs_triangle") (at sa n) (at sb n))))))))))))))))))))))

(defn- install-limits! []
  (let [symm-r (fn [x y e] (t/app (k/const "Eq.symm" l1) R x y e))
        ;; ∃ δ, 0 < δ ∧ ∀ y, 0 < |y − x| → |y − x| < δ → |f y − L| < ε
        near (fn [f x L eps]
               (t/exists' R (t/lambda [[d R]]
                              (t/and' (lt zero d)
                                      (t/forall [[y R]]
                                        (implies (lt zero (abs (sub y x))) (lt (abs (sub y x)) d)
                                                 (lt (abs (sub (t/app f y) L)) eps)))))))
        near-body (fn [f x L eps d]
                    (t/forall [[y R]]
                      (implies (lt zero (abs (sub y x))) (lt (abs (sub y x)) d)
                               (lt (abs (sub (t/app f y) L)) eps))))
        near-intro (fn [f x L eps d hd hall]
                     (t/exists-intro R (t/lambda [[d' R]]
                                         (t/and' (lt zero d') (near-body f x L eps d'))) d
                                     (t/and-intro (lt zero d) (near-body f x L eps d) hd hall)))
        near-elim (fn [f x L eps goal h k]
                    (t/exists-elim R (t/lambda [[d R]] (t/and' (lt zero d) (near-body f x L eps d)))
                                   goal h
                                   (t/lambda [[d R] [hd (t/and' (lt zero d) (near-body f x L eps d))]]
                                     (k d (t/and-left (lt zero d) (near-body f x L eps d) hd)
                                        (t/and-right (lt zero d) (near-body f x L eps d) hd)))))
        ;; ∃ δ, 0 < δ ∧ ∀ y, |y − x| < δ → |f y − f x| < ε
        cont-body (fn [f x eps d]
                    (t/forall [[y R]]
                      (implies (lt (abs (sub y x)) d) (lt (abs (sub (t/app f y) (t/app f x))) eps))))
        cont-near (fn [f x eps]
                    (t/exists' R (t/lambda [[d R]] (t/and' (lt zero d) (cont-body f x eps d)))))
        cont-intro (fn [f x eps d hd hall]
                     (t/exists-intro R (t/lambda [[d' R]] (t/and' (lt zero d') (cont-body f x eps d'))) d
                                     (t/and-intro (lt zero d) (cont-body f x eps d) hd hall)))
        pick-min (fn [a b ha hb goal k]
                   (let [body (fn [cc] (t/and' (lt zero cc) (t/and' (lt cc a) (lt cc b))))]
                     (t/exists-elim R (t/lambda [[cc R]] (body cc)) goal
                                    (t/app (c "exists_pos_lt_both") a b ha hb)
                                    (t/lambda [[cc R] [hc (body cc)]]
                                      (k cc (t/and-left (lt zero cc) (t/and' (lt cc a) (lt cc b)) hc)
                                         (t/and-left (lt cc a) (lt cc b)
                                                     (t/and-right (lt zero cc) (t/and' (lt cc a) (lt cc b)) hc))
                                         (t/and-right (lt cc a) (lt cc b)
                                                      (t/and-right (lt zero cc) (t/and' (lt cc a) (lt cc b)) hc)))))))]
    (define! "TendsToAt" (t/arrow Fn (t/arrow R (t/arrow R t/prop)))
      (t/lambda [[f Fn] [x R] [L R]]
        (t/forall [[eps R]] (t/arrow (lt zero eps) (near f x L eps)))))
    (define! "ContinuousAt" (t/arrow Fn (t/arrow R t/prop))
      (t/lambda [[f Fn] [x R]]
        (t/forall [[eps R]] (t/arrow (lt zero eps) (cont-near f x eps)))))
    (define! "Continuous" (t/arrow Fn t/prop)
      (t/lambda [[f Fn]] (t/forall [[x R]] (continuous-at f x))))
    ;; constants and the identity
    (theorem! "tendsto_const"
      (t/forall [[cst R] [x R]] (tends-to-at (t/lam "y" R (fn [_] cst)) x cst))
      (t/lambda [[cst R] [x R] [eps R] [he (lt zero eps)]]
        (let [f (t/lam "y" R (fn [_] cst))]
          (near-intro f x cst eps one (c "zero_lt_one")
                      (t/lambda [[y R] [_h1 (lt zero (abs (sub y x)))] [_h2 (lt (abs (sub y x)) one)]]
                        (t/transport-at R l1 (t/lambda [[z R]] (lt z eps)) zero (abs (sub cst cst))
                                        (symm-r (abs (sub cst cst)) zero (t/app (c "abs_sub_self") cst))
                                        he))))))
    (theorem! "tendsto_id"
      (t/forall [[x R]] (tends-to-at (t/lam "y" R identity) x x))
      (t/lambda [[x R] [eps R] [he (lt zero eps)]]
        (let [f (t/lam "y" R identity)]
          (near-intro f x x eps eps he
                      (t/lambda [[y R] [_h1 (lt zero (abs (sub y x)))] [h2 (lt (abs (sub y x)) eps)]]
                        h2)))))
    ;; sums
    (theorem! "tendsto_add"
      (t/forall [[f Fn] [g Fn] [x R] [L R] [M R]]
        (implies (tends-to-at f x L) (tends-to-at g x M)
                 (tends-to-at (t/lam "y" R #(add (t/app f %) (t/app g %))) x (add L M))))
      (t/lambda [[f Fn] [g Fn] [x R] [L R] [M R]
                 [hf (tends-to-at f x L)] [hg (tends-to-at g x M)]
                 [eps R] [he (lt zero eps)]]
        (let [h (t/lam "y" R #(add (t/app f %) (t/app g %)))
              e2 (mul half eps)
              he2 (t/app (c "half_pos") eps he)
              goal (near h x (add L M) eps)]
          (t/with-cont
            [[d1 hd1 hall1] (near-elim f x L e2 goal (t/app hf e2 he2))
             [d2 hd2 hall2] (near-elim g x M e2 goal (t/app hg e2 he2))
             [d hd hda hdb] (pick-min d1 d2 hd1 hd2 goal)]
            (near-intro h x (add L M) eps d hd
              (t/lambda [[y R] [hy0 (lt zero (abs (sub y x)))] [hy (lt (abs (sub y x)) d)]]
                (let [b1 (t/app hall1 y hy0 (t/app (c "lt_trans") (abs (sub y x)) d d1 hy hda))
                      b2 (t/app hall2 y hy0 (t/app (c "lt_trans") (abs (sub y x)) d d2 hy hdb))
                      sum (t/app (c "dist_add_lt") (t/app f y) L (t/app g y) M e2 e2 b1 b2)]
                  (t/transport-at R l1
                    (t/lambda [[z R]] (lt (abs (sub (add (t/app f y) (t/app g y)) (add L M))) z))
                    (add e2 e2) eps (t/app (c "half_add_half") eps) sum))))))))
    (theorem! "tendsto_neg"
      (t/forall [[f Fn] [x R] [L R]]
        (implies (tends-to-at f x L) (tends-to-at (t/lam "y" R #(neg (t/app f %))) x (neg L))))
      (t/lambda [[f Fn] [x R] [L R] [hf (tends-to-at f x L)] [eps R] [he (lt zero eps)]]
        (let [h (t/lam "y" R #(neg (t/app f %)))
              goal (near h x (neg L) eps)]
          (near-elim f x L eps goal (t/app hf eps he)
                     (fn [d hd hall]
                       (near-intro h x (neg L) eps d hd
                                   (t/lambda [[y R] [hy0 (lt zero (abs (sub y x)))] [hy (lt (abs (sub y x)) d)]]
                                     (t/transport-at R l1 (t/lambda [[z R]] (lt z eps))
                                                     (abs (sub (t/app f y) L))
                                                     (abs (sub (neg (t/app f y)) (neg L)))
                                                     (symm-r (abs (sub (neg (t/app f y)) (neg L)))
                                                             (abs (sub (t/app f y) L))
                                                             (t/app (c "dist_neg") (t/app f y) L))
                                                     (t/app hall y hy0 hy)))))))))
    ;; products: f y·g y − L·M = (f y − L)·g y + L·(g y − M)
    (theorem! "tendsto_mul"
      (t/forall [[f Fn] [g Fn] [x R] [L R] [M R]]
        (implies (tends-to-at f x L) (tends-to-at g x M)
                 (tends-to-at (t/lam "y" R #(mul (t/app f %) (t/app g %))) x (mul L M))))
      (t/lambda [[f Fn] [g Fn] [x R] [L R] [M R]
                 [hf (tends-to-at f x L)] [hg (tends-to-at g x M)]
                 [eps R] [he (lt zero eps)]]
        (let [h (t/lam "y" R #(mul (t/app f %) (t/app g %)))
              goal (near h x (mul L M) eps)
              A (add (abs M) one) B (add (abs L) one)
              hA (t/app (c "abs_add_one_pos") M) hB (t/app (c "abs_add_one_pos") L)
              e2 (mul half eps)
              he2 (t/app (c "half_pos") eps he)
              t1 (mul (inv A) e2)
              t2 (mul (inv B) e2)
              ht1 (t/app (c "mul_pos") (inv A) e2 (t/app (c "inv_pos") A hA) he2)
              ht2 (t/app (c "mul_pos") (inv B) e2 (t/app (c "inv_pos") B hB) he2)]
          (near-elim f x L t1 goal (t/app hf t1 ht1)
                     (fn [d1 hd1 hall1]
                       ;; g must stay within min(1, t2) of M
                       (pick-min one t2 (c "zero_lt_one") ht2 goal
                                 (fn [cc hc hc1 hct]
                                   (near-elim g x M cc goal (t/app hg cc hc)
                                              (fn [d2 hd2 hall2]
                                                (pick-min d1 d2 hd1 hd2 goal
                                                          (fn [d hd hda hdb]
                                                            (near-intro h x (mul L M) eps d hd
                                                                        (t/lambda [[y R] [hy0 (lt zero (abs (sub y x)))] [hy (lt (abs (sub y x)) d)]]
                                                                          (let [fy (t/app f y) gy (t/app g y)
                                                                                b1 (t/app hall1 y hy0 (t/app (c "lt_trans") (abs (sub y x)) d d1 hy hda))
                                                                                b2 (t/app hall2 y hy0 (t/app (c "lt_trans") (abs (sub y x)) d d2 hy hdb))
                                                                                ;; |g y| < |M| + 1
                                                                                hgy (t/app (c "abs_lt_add") M gy one
                                                                                           (t/app (c "lt_trans") (abs (sub gy M)) cc one b2 hc1))
                                                                                ;; |(f y − L)·g y| < t1·A = ε/2
                                                                                p1 (t/app (c "abs_mul_lt") (sub fy L) gy t1 A b1 hgy)
                                                                                p1' (t/transport-at R l1
                                                                                                    (t/lambda [[z R]] (lt (abs (mul (sub fy L) gy)) z))
                                                                                                    (mul t1 A) e2
                                                                                                    (t/app (k/const "Eq.trans" l1) R (mul t1 A) (mul A t1) e2
                                                                                                           (t/app (c "mul_comm") t1 A)
                                                                                                           (t/app (c "mul_inv_mul") A e2 hA))
                                                                                                    p1)
                                                                                ;; |L·(g y − M)| < B·t2 = ε/2
                                                                                p2 (t/app (c "abs_mul_lt") L (sub gy M) B t2
                                                                                          (t/app (c "abs_lt_abs_add_one") L)
                                                                                          (t/app (c "lt_trans") (abs (sub gy M)) cc t2 b2 hct))
                                                                                p2' (t/transport-at R l1
                                                                                                    (t/lambda [[z R]] (lt (abs (mul L (sub gy M))) z))
                                                                                                    (mul B t2) e2
                                                                                                    (t/app (c "mul_inv_mul") B e2 hB)
                                                                                                    p2)
                                                                                sum (t/app (c "abs_add_lt") (mul (sub fy L) gy) (mul L (sub gy M)) e2 e2 p1' p2')
                                                                                sum' (t/transport-at R l1
                                                                                                     (t/lambda [[z R]] (lt (abs (add (mul (sub fy L) gy) (mul L (sub gy M)))) z))
                                                                                                     (add e2 e2) eps
                                                                                                     (t/app (c "half_add_half") eps)
                                                                                                     sum)]
                                                                            (t/transport-at R l1
                                                                                            (t/lambda [[z R]] (lt (abs z) eps))
                                                                                            (add (mul (sub fy L) gy) (mul L (sub gy M)))
                                                                                            (sub (mul fy gy) (mul L M))
                                                                                            (symm-r (sub (mul fy gy) (mul L M))
                                                                                                    (add (mul (sub fy L) gy) (mul L (sub gy M)))
                                                                                                    (t/app (c "mul_sub_decomp") fy gy L M))
                                                                                            sum')))))))))))))))
    ;; uniqueness: two limits would be within every ε of each other
    (theorem! "tendsto_unique"
      (t/forall [[f Fn] [x R] [L R] [M R]]
        (implies (tends-to-at f x L) (tends-to-at f x M) (eq-r L M)))
      (t/lambda [[f Fn] [x R] [L R] [M R] [h1 (tends-to-at f x L)] [h2 (tends-to-at f x M)]]
        (t/app (k/const "Classical.byCases") (eq-r L M) (eq-r L M)
               (t/lam "he" (eq-r L M) identity)
               (t/lam "hne" (t/not' (eq-r L M))
                      (fn [hne]
                        (let [D (abs (sub L M))
                              hD (t/app (c "abs_pos_of_ne") L M hne)
                              e2 (mul half D)
                              he2 (t/app (c "half_pos") D hD)
                              goal (eq-r L M)]
                          (near-elim f x L e2 goal (t/app h1 e2 he2)
                                     (fn [d1 hd1 hall1]
                                       (near-elim f x M e2 goal (t/app h2 e2 he2)
                                                  (fn [d2 hd2 hall2]
                                                    (pick-min d1 d2 hd1 hd2 goal
                                                              (fn [d hd hda hdb]
                                                                ;; y = x + δ/2 is within δ of x and distinct from it
                                                                (let [y (add x (mul half d))
                                                                      hhalf (t/app (c "half_pos") d hd)
                                                                      ;; |y − x| = δ/2
                                                                      ydist (t/app (k/const "Eq.trans" l1) R
                                                                                   (abs (sub y x)) (abs (mul half d)) (mul half d)
                                                                                   (t/app (k/const "congrArg" l1 l1) R R (sub y x) (mul half d) (c "abs")
                                                                                          (t/app (c "add_sub_cancel_left") x (mul half d)))
                                                                                   (t/app (c "abs_of_pos") (mul half d) hhalf))
                                                                      hy0 (t/transport-at R l1 (t/lambda [[z R]] (lt zero z))
                                                                                          (mul half d) (abs (sub y x))
                                                                                          (symm-r (abs (sub y x)) (mul half d) ydist)
                                                                                          hhalf)
                                                                      hyd (t/transport-at R l1 (t/lambda [[z R]] (lt z d))
                                                                                          (mul half d) (abs (sub y x))
                                                                                          (symm-r (abs (sub y x)) (mul half d) ydist)
                                                                                          (t/app (c "half_lt_self") d hd))
                                                                      bL (t/app hall1 y hy0 (t/app (c "lt_trans") (abs (sub y x)) d d1 hyd hda))
                                                                      bM (t/app hall2 y hy0 (t/app (c "lt_trans") (abs (sub y x)) d d2 hyd hdb))
                                                                      ;; |L − M| < D/2 + D/2 = D, contradicting irreflexivity
                                                                      tri (t/app (c "dist_triangle_lt") L (t/app f y) M e2 e2
                                                                                 (t/transport-at R l1 (t/lambda [[z R]] (lt z e2))
                                                                                                 (abs (sub (t/app f y) L)) (abs (sub L (t/app f y)))
                                                                                                 (t/app (c "abs_sub_comm") (t/app f y) L)
                                                                                                 bL)
                                                                                 bM)
                                                                      tri' (t/transport-at R l1 (t/lambda [[z R]] (lt D z))
                                                                                           (add e2 e2) D (t/app (c "half_add_half") D)
                                                                                           tri)]
                                                                  (t/false-elim goal (t/app (c "lt_irrefl") D tri')))))))))))))))
    ;; the punctured limit at the value gives (unpunctured) continuity
    (theorem! "continuousAt_of_tendsto"
      (t/forall [[f Fn] [x R]]
        (implies (tends-to-at f x (t/app f x)) (continuous-at f x)))
      (t/lambda [[f Fn] [x R] [h (tends-to-at f x (t/app f x))] [eps R] [he (lt zero eps)]]
        (let [fx (t/app f x)
              goal (cont-near f x eps)]
          (near-elim f x fx eps goal (t/app h eps he)
                     (fn [d hd hall]
                       (cont-intro f x eps d hd
                                   (t/lambda [[y R] [hy (lt (abs (sub y x)) d)]]
                                     (t/app (k/const "Classical.byCases") (eq-r y x)
                                            (lt (abs (sub (t/app f y) fx)) eps)
                                            ;; y = x: the distance is 0
                                            (t/lam "hyx" (eq-r y x)
                                                   (fn [hyx]
                                                     (t/transport-at R l1
                                                                     (t/lambda [[z R]] (lt (abs (sub (t/app f z) fx)) eps))
                                                                     x y (symm-r y x hyx)
                                                                     (t/transport-at R l1 (t/lambda [[z R]] (lt z eps))
                                                                                     zero (abs (sub fx fx))
                                                                                     (symm-r (abs (sub fx fx)) zero
                                                                                             (t/app (c "abs_sub_self") fx))
                                                                                     he))))
                                            (t/lam "hyx" (t/not' (eq-r y x))
                                                   (fn [hyx]
                                                     (t/app hall y (t/app (c "abs_pos_of_ne") y x hyx) hy)))))))))))
    (theorem! "continuous_const"
      (t/forall [[cst R]] (continuous (t/lam "y" R (fn [_] cst))))
      (t/lambda [[cst R] [x R]]
        (t/app (c "continuousAt_of_tendsto") (t/lam "y" R (fn [_] cst)) x
               (t/app (c "tendsto_const") cst x))))
    (theorem! "continuous_id" (continuous (t/lam "y" R identity))
      (t/lambda [[x R]]
        (t/app (c "continuousAt_of_tendsto") (t/lam "y" R identity) x (t/app (c "tendsto_id") x))))))

;; ## Installation

(defn install!
  "Installs Cauchy sequences over `Q`, their equivalence and the quotient `R`.
  Idempotent."
  []
  (q/install!)
  (locking k/install-lock
    (define! "Cauchy" (t/arrow Seq t/prop)
      (t/lambda [[s Seq]]
        (t/forall [[eps Q]]
          (implies (pos eps)
                   (t/exists' Nat
                              (t/lambda [[N Nat]]
                                (t/forall [[m Nat] [n Nat]]
                                  (implies (nat-le N m) (nat-le N n)
                                           (q/lt (dist (t/app s m) (t/app s n)) eps)))))))))
    (define! "CSeq" t/type0 (t/app (k/const "Subtype" l1) Seq (c "Cauchy")))
    (define! "Equiv" (t/arrow CSeq (t/arrow CSeq t/prop))
      (t/lambda [[s CSeq] [u CSeq]]
        (t/forall [[eps Q]]
          (implies (pos eps) (eventually #(q/lt (dist (at s %) (at u %)) eps))))))

    (theorem! "equiv_refl" (t/forall [[s CSeq]] (equiv s s))
      (t/lambda [[s CSeq] [eps Q] [h (pos eps)]]
        (eventually-intro #(q/lt (dist (at s %) (at s %)) eps) (e/lit-nat 0)
                          (t/lambda [[n Nat] [_hn (nat-le (e/lit-nat 0) n)]]
                            (dist-self-lt (at s n) eps h)))))

    (theorem! "equiv_symm" (t/forall [[s CSeq] [u CSeq]] (implies (equiv s u) (equiv u s)))
      (t/lambda [[s CSeq] [u CSeq] [h (equiv s u)] [eps Q] [he (pos eps)]]
        (let [P #(q/lt (dist (at s %) (at u %)) eps)
              P' #(q/lt (dist (at u %) (at s %)) eps)]
          (eventually-elim P (eventually P') (t/app h eps he)
                           (fn [N hN]
                             (eventually-intro P' N
                                               (t/lambda [[n Nat] [hn (nat-le N n)]]
                                                 (t/transport-at Q l1 (t/lambda [[z Q]] (q/lt z eps))
                                                                 (dist (at s n) (at u n)) (dist (at u n) (at s n))
                                                                 (t/app (qc "abs_sub_comm") (at s n) (at u n))
                                                                 (t/app hN n hn)))))))))

    (theorem! "equiv_trans"
      (t/forall [[s CSeq] [u CSeq] [v CSeq]] (implies (equiv s u) (equiv u v) (equiv s v)))
      (t/lambda [[s CSeq] [u CSeq] [v CSeq] [h1 (equiv s u)] [h2 (equiv u v)] [eps Q] [he (pos eps)]]
        (let [e2 (q/mul q/half eps)
              he2 (t/app (qc "half_pos_of_pos") eps he)
              P1 #(q/lt (dist (at s %) (at u %)) e2)
              P2 #(q/lt (dist (at u %) (at v %)) e2)
              P #(q/lt (dist (at s %) (at v %)) eps)]
          (eventually-elim P1 (eventually P) (t/app h1 e2 he2)
                           (fn [N1 hN1]
                             (eventually-elim P2 (eventually P) (t/app h2 e2 he2)
                                              (fn [N2 hN2]
                                                (eventually-intro P (nat-add N1 N2)
                                                                  (t/lambda [[n Nat] [hn (nat-le (nat-add N1 N2) n)]]
                                                                    (let [[hn1 hn2] (threshold-le N1 N2 n hn)
                                                                          d1 (dist (at s n) (at u n))
                                                                          d2 (dist (at u n) (at v n))
                                                                          sum (half-split d1 d2 eps
                                                                                          (t/app hN1 n hn1)
                                                                                          (t/app hN2 n hn2))
                                                                          tri (t/app (qc "dist_triangle") (at s n) (at u n) (at v n))]
                                                                      (t/app (qc "lt_of_le_of_lt")
                                                                             (dist (at s n) (at v n)) (q/add d1 d2) eps
                                                                             tri sum)))))))))))

    (define! "R" t/type0 (t/quot-type CSeq (c "Equiv")))
    (define! "constSeq" (t/arrow Q Seq) (t/lambda [[x Q]] (t/lam "n" Nat (fn [_] x))))
    (theorem! "const_cauchy" (t/forall [[x Q]] (cauchy (t/app (c "constSeq") x)))
      (t/lambda [[x Q] [eps Q] [h (pos eps)]]
        (let [body (fn [N] (t/forall [[m Nat] [n Nat]]
                              (implies (nat-le N m) (nat-le N n) (q/lt (dist x x) eps))))]
          (t/exists-intro Nat (t/lambda [[N Nat]] (body N)) (e/lit-nat 0)
                          (t/lambda [[m Nat] [n Nat]
                                     [_hm (nat-le (e/lit-nat 0) m)]
                                     [_hn (nat-le (e/lit-nat 0) n)]]
                            (dist-self-lt x eps h))))))
    (define! "ofQ" (t/arrow Q R)
      (t/lambda [[x Q]]
        (t/quot-mk CSeq (c "Equiv")
                   (t/app (k/const "Subtype.mk" l1) Seq (c "Cauchy")
                          (t/app (c "constSeq") x) (t/app (c "const_cauchy") x)))))
    (install-add-neg!)
    (install-mul!)
    (install-ring-laws!)
    (install-order!)
    (install-order-laws!)
    (install-apart!)
    (install-trichotomy!)
    (install-archimedean!)
    (install-inv!)
    (install-density!)
    (install-abs!)
    (install-complete!)
    (install-order-toolkit!)
    (install-limit-lemmas!)
    (install-limits!))
  :installed)
