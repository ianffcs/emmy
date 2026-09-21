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
  (t/exists' Nat (t/lambda [[N Nat]] (t/forall [[n Nat]] (t/arrow (nat-le N n) (P n))))))

(defn- eventually-intro
  "Proof of `eventually P` from the threshold `N` and `f : ∀ n, N ≤ n → P n`."
  [P N f]
  (t/exists-intro Nat (t/lambda [[M Nat]] (t/forall [[n Nat]] (t/arrow (nat-le M n) (P n)))) N f))

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
  (let [names (take n ["x" "y" "z" "w"])
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
    (install-archimedean!))
  :installed)
