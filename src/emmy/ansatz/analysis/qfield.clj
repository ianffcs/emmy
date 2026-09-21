#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.qfield
  "ℚ as a quotient type in the Ansatz kernel, with its ring laws as genuine
  equalities.

  ```
  Emmy.Analysis.Q.Q := Quot Rational.Rep Rational.Equiv
  mk, zero, one, add, mul, neg, sub
  add_comm, add_assoc, zero_add, add_left_neg,
  mul_comm, mul_assoc, one_mul, left_distrib
  ```

  Operations are lifted from representatives with [[lift1]]/[[lift2]], which
  discharge `Quot.lift`'s respect obligation with the representative
  congruence lemmas (`Rational.add_congr`, …). Laws are proved by `Quot.ind`
  over each variable and `Quot.sound` of a cross-multiplied identity on
  representatives, closed by `int_ring` ([[quot-law!]])."
  (:refer-clojure :exclude [abs])
  (:require [ansatz.kernel.expr]
            [ansatz.kernel.level :as level]
            [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.order :as o]
            [emmy.ansatz.analysis.rational :as rat]
            [emmy.ansatz.core :as k]))

(def ^:private l1 (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.Q.")
(defn- c [s] (k/const (str prefix s)))
(defn- r [s] (k/const (str "Emmy.Analysis.Rational." s)))

(def rep "The kernel type of rational representatives." (r "Rep"))
(def ^:private equiv-rel (r "Equiv"))
(def Q "The kernel type ℚ." (c "Q"))

(defn- theorem! [label type proof]
  (when-not (k/installed? (str prefix label))
    (t/install-declaration! :thm (str prefix label) type proof)))

(defn- define! [label type value]
  (when-not (k/installed? (str prefix label))
    (t/install-declaration! :def (str prefix label) type value)))

;; ## Representative expressions
;;
;; A representative expression is `{:rep term :num n :den d}`, where `n` and
;; `d` are its numerator and denominator spelled exactly as they reduce, so
;; cross-multiplied identities can be proved over the atoms num/den of leaves.

(defn leaf [a] {:rep a :num (t/app (r "num") a) :den (t/app (r "den") a)})

(defn radd [x y]
  {:rep (t/app (r "add") (:rep x) (:rep y))
   :num (k/add (k/mul (:num x) (:den y)) (k/mul (:num y) (:den x)))
   :den (k/mul (:den x) (:den y))})

(defn rmul [x y]
  {:rep (t/app (r "mul") (:rep x) (:rep y))
   :num (k/mul (:num x) (:num y))
   :den (k/mul (:den x) (:den y))})

(defn rneg [x]
  {:rep (t/app (r "neg") (:rep x)) :num (k/neg (:num x)) :den (:den x)})

(def rzero {:rep (c "repZero") :num k/zero :den k/one})
(def rone {:rep (c "repOne") :num k/one :den k/one})

(defn equiv-proof
  "Proof of `Rational.Equiv x y` for representative expressions whose
  cross-multiplied numerators agree as a ring identity."
  [x y]
  (:term (alg/prove-eq (k/mul (:num x) (:den y)) (k/mul (:num y) (:den x)))))

;; ## Lifting

(defn mk "`Quot.mk Equiv a : Q`." [a] (t/quot-mk rep equiv-rel a))

(defn- sound [a b h] (t/quot-sound rep equiv-rel a b h))

(defn lift1
  "The kernel term `Q → Q` lifting the representative operation `op` (a
  constant), given its congruence lemma `congr : ∀ a b, a ≈ b → op a ≈ op b`."
  [op congr]
  (t/lambda [[q Q]]
    (t/app (t/quot-lift rep equiv-rel Q
                        (t/lambda [[a rep]] (mk (t/app op a)))
                        (t/lambda [[a rep] [b rep] [h (rat/equiv a b)]]
                          (sound (t/app op a) (t/app op b) (t/app congr a b h))))
           q)))

(defn lift2
  "The kernel term `Q → Q → Q` lifting the binary representative operation
  `op`, given `congr : ∀ a a' b b', a ≈ a' → b ≈ b' → op a b ≈ op a' b'`."
  [op congr]
  (let [refl #(t/app (r "equiv_refl") %)
        inner (fn [a q2]
                (t/app (t/quot-lift rep equiv-rel Q
                                    (t/lambda [[b rep]] (mk (t/app op a b)))
                                    (t/lambda [[b rep] [b' rep] [h (rat/equiv b b')]]
                                      (sound (t/app op a b) (t/app op a b')
                                             (t/app congr a a b b' (refl a) h))))
                       q2))]
    (t/lambda [[q1 Q] [q2 Q]]
      (t/app (t/quot-lift rep equiv-rel Q
                          (t/lambda [[a rep]] (inner a q2))
                          (t/lambda [[a rep] [a' rep] [h (rat/equiv a a')]]
                            (t/app (t/quot-ind rep equiv-rel
                                               (t/lambda [[q Q]] (k/eq-at Q l1 (inner a q) (inner a' q)))
                                               (t/lambda [[b rep]]
                                                 (sound (t/app op a b) (t/app op a' b)
                                                        (t/app congr a a' b b h (refl b)))))
                                   q2)))
             q1))))

(defn quot-ind-all
  "Proof of `∀ q₁ … qₙ : Q, P q₁ … qₙ` given as the proof terms for
  `P (mk a₁) … (mk aₙ)`: `motive` maps n `Q` terms to a proposition and
  `leaf` maps n representative fvars to a proof. `qs` are the bound `Q` fvars."
  [qs motive leaf]
  (letfn [(go [done remaining]
            (if (empty? remaining)
              (leaf done)
              (let [q (first remaining)
                    more (rest remaining)]
                (t/app (t/quot-ind rep equiv-rel
                                   (t/lambda [[x Q]] (apply motive (concat (map mk done) [x] more)))
                                   (t/lambda [[a rep]] (go (conj done a) more)))
                       q))))]
    (go [] (vec qs))))

(defn pis
  "`∀ x₁ … xₙ : ty, body` where `body-fn` receives the n bound fvars."
  [names ty body-fn]
  (letfn [(go [names acc]
            (if (empty? names)
              (body-fn acc)
              (t/pi (first names) ty (fn [x] (go (rest names) (conj acc x))))))]
    (go names [])))

(defn lams
  "`λ x₁ … xₙ : ty, body` where `body-fn` receives the n bound fvars."
  [names ty body-fn]
  (letfn [(go [names acc]
            (if (empty? names)
              (body-fn acc)
              (t/lam (first names) ty (fn [x] (go (rest names) (conj acc x))))))]
    (go names [])))

(def ^:private var-names ["p" "q" "s" "u"])

(defn quot-law!
  "Installs `∀ q₁ … qₙ : Q, lhs = rhs`, where `q-lhs`/`q-rhs` build the `Q`
  sides from the bound variables and `rep-lhs`/`rep-rhs` build the matching
  representative expressions from [[leaf]]s."
  [label n q-lhs q-rhs rep-lhs rep-rhs]
  (let [names (take n var-names)
        statement (fn [qs] (k/eq-at Q l1 (apply q-lhs qs) (apply q-rhs qs)))]
    (theorem! label
      (pis names Q statement)
      (lams names Q
            (fn [qs]
              (quot-ind-all qs
                            (fn [& qs'] (statement qs'))
                            (fn [as]
                              (let [leaves (map leaf as)
                                    x (apply rep-lhs leaves)
                                    y (apply rep-rhs leaves)]
                                (sound (:rep x) (:rep y) (equiv-proof x y))))))))))

;; ## Operations

(defn add [p q] (t/app (c "add") p q))
(defn mul [p q] (t/app (c "mul") p q))
(defn neg [p] (t/app (c "neg") p))
(defn sub [p q] (t/app (c "sub") p q))
(defn lt [p q] (t/app (c "lt") p q))
(defn le [p q] (t/app (c "le") p q))
(defn abs [p] (t/app (c "abs") p))
(defn of-int [m] (t/app (c "ofInt") m))
(def zero (c "zero"))
(def one (c "one"))
(def half (c "half"))

;; ## Order on representatives

(defn- rnum [a] (t/app (r "num") a))
(defn- rden [a] (t/app (r "den") a))
(defn- den-pos [a] (t/app (r "den_pos") a))
(defn- int-mul-pos [x y hx hy] (t/app (k/const "Int.mul_pos") x y hx hy))

(defn rel-prop
  "`x.num · y.den REL y.num · x.den` for representative expressions, where
  `rel` is `o/lt` or `o/le`."
  [rel x y]
  (rel (k/mul (:num x) (:den y)) (k/mul (:num y) (:den x))))

(defn- scale-eq
  "From the `Int` equation proof map `h : l = r`, a proof of `l·z = r·z`."
  [h z]
  (alg/linear-combination (k/mul (:lhs h) z) (k/mul (:rhs h) z) [[z h]]))

(def ^:private relations
  ;; rel builder, multiply-by-positive lemma form, cancel lemma
  {:lt {:rel o/lt
        :mono (fn [x y z h hz] [(o/lt (k/mul z x) (k/mul z y))
                                (t/app (k/const "Int.mul_lt_mul_of_pos_left") x y z h hz)])
        :cancel "Emmy.Analysis.Int.lt_of_mul_lt_mul_right"}
   :le {:rel o/le
        :mono (fn [x y z h hz] [(o/le (k/mul z x) (k/mul z y))
                                (t/app (k/const "Int.mul_le_mul_of_nonneg_left") x y z h
                                       (t/app (k/const "Int.le_of_lt") k/zero z hz))])
        :cancel "Emmy.Analysis.Int.le_of_mul_le_mul_right"}})

(defn- rel-congr-proof
  "Proof of `REL a' b'` from `ha : a ≈ a'`, `hb : b ≈ b'` and `h : REL a b`."
  [kind a a' b b' ha hb h]
  (let [{:keys [rel mono cancel]} (relations kind)
        x (k/mul (rnum a) (rden b)) y (k/mul (rnum b) (rden a))
        x' (k/mul (rnum a') (rden b')) y' (k/mul (rnum b') (rden a'))
        z1 (k/mul (rden a') (rden b'))
        z2 (k/mul (rden a) (rden b))
        [f1-prop f1] (mono x y z1 h (int-mul-pos (rden a') (rden b') (den-pos a') (den-pos b')))
        e1 (scale-eq {:lhs (k/mul (rnum a) (rden a')) :rhs (k/mul (rnum a') (rden a)) :term ha}
                     (k/mul (rden b') (rden b)))
        e2 (scale-eq {:lhs (k/mul (rnum b) (rden b')) :rhs (k/mul (rnum b') (rden b)) :term hb}
                     (k/mul (rden a) (rden a')))
        goal (rel (k/mul x' z2) (k/mul y' z2))
        g (o/by-omega goal [[f1-prop f1]
                            [(k/eq (:lhs e1) (:rhs e1)) (:term e1)]
                            [(k/eq (:lhs e2) (:rhs e2)) (:term e2)]])]
    (t/app (k/const cancel) x' y' z2 (int-mul-pos (rden a) (rden b) (den-pos a) (den-pos b)) g)))

(defn lift2-prop
  "The kernel term `Q → Q → Prop` lifting the representative relation `rel`
  (a constant), given `congr : ∀ a a' b b', a ≈ a' → b ≈ b' → rel a b → rel a' b'`."
  [rel congr]
  (let [refl #(t/app (r "equiv_refl") %)
        symm #(t/app (r "equiv_symm") %1 %2 %3)
        rab #(t/app rel %1 %2)
        iff-of (fn [p q mp mpr] (t/propext' p q (t/iff-intro p q mp mpr)))
        inner (fn [a q2]
                (t/app (t/quot-lift-prop rep equiv-rel
                                         (t/lambda [[b rep]] (rab a b))
                                         (t/lambda [[b rep] [b' rep] [h (rat/equiv b b')]]
                                           (iff-of (rab a b) (rab a b')
                                                   (t/lam "x" (rab a b)
                                                          #(t/app congr a a b b' (refl a) h %))
                                                   (t/lam "x" (rab a b')
                                                          #(t/app congr a a b' b (refl a) (symm b b' h) %)))))
                       q2))]
    (t/lambda [[q1 Q] [q2 Q]]
      (t/app (t/quot-lift-prop rep equiv-rel
                               (t/lambda [[a rep]] (inner a q2))
                               (t/lambda [[a rep] [a' rep] [h (rat/equiv a a')]]
                                 (t/app (t/quot-ind rep equiv-rel
                                                    (t/lambda [[q Q]] (k/eq-at t/prop l1 (inner a q) (inner a' q)))
                                                    (t/lambda [[b rep]]
                                                      (iff-of (rab a b) (rab a' b)
                                                              (t/lam "x" (rab a b)
                                                                     #(t/app congr a a' b b h (refl b) %))
                                                              (t/lam "x" (rab a' b)
                                                                     #(t/app congr a' a b b (symm a a' h) (refl b) %)))))
                                        q2)))
             q1))))

(defn q-theorem!
  "Installs `∀ q₁ … qₙ : Q, P q₁ … qₙ`. `statement` maps the `Q` fvars to
  `P`; `leaf` maps representative fvars `a₁ … aₙ` to a proof of
  `P (mk a₁) … (mk aₙ)`."
  [label n statement leaf]
  (let [names (take n var-names)]
    (theorem! label
      (pis names Q statement)
      (lams names Q (fn [qs] (quot-ind-all qs (fn [& qs'] (statement qs')) leaf))))))

(defn- implies [& props] (reduce (fn [acc p] (t/arrow p acc)) (last props) (reverse (butlast props))))

;; ## Absolute value on representatives

(defn rabs [x]
  {:rep (t/app (c "repAbs") (:rep x)) :num (o/abs (:num x)) :den (:den x)})

(defn- abs-pos-map
  "Proof map `abs d = d` for the positive `d` (from `hd : 0 < d`)."
  [d hd]
  {:lhs (o/abs d) :rhs d :term (t/app (k/const "Emmy.Analysis.Int.abs_of_pos") d hd)})

(defn- abs-mul-map [x y]
  {:lhs (o/abs (k/mul x y)) :rhs (k/mul (o/abs x) (o/abs y))
   :term (t/app (k/const "Emmy.Analysis.Int.abs_mul") x y)})

(defn- abs-congr-proof
  "Proof of `|na|·da' = |na'|·da` from `h : na·da' = na'·da`."
  [a a' h]
  (let [na (rnum a) da (rden a) na' (rnum a') da' (rden a')
        congr-abs {:lhs (o/abs (k/mul na da')) :rhs (o/abs (k/mul na' da))
                   :term (t/app (k/const "congrArg" l1 l1) k/int-type k/int-type
                                (k/mul na da') (k/mul na' da) (k/const "Emmy.Analysis.Int.abs") h)}]
    (:term (k/trans (k/congr-mul (k/refl (o/abs na)) (k/symm (abs-pos-map da' (den-pos a'))))
                    (k/symm (abs-mul-map na da'))
                    congr-abs
                    (abs-mul-map na' da)
                    (k/congr-mul (k/refl (o/abs na')) (abs-pos-map da (den-pos a)))))))

(defn- install-order! []
  (let [rrel (fn [kind] (fn [a b] (rel-prop (:rel (relations kind)) (leaf a) (leaf b))))]
    (doseq [kind [:lt :le]
            :let [nm (name kind)
                  rep-rel (c (str "rep" (if (= kind :lt) "Lt" "Le")))]]
      (define! (str "rep" (if (= kind :lt) "Lt" "Le")) (t/arrow rep (t/arrow rep t/prop))
        (t/lambda [[a rep] [b rep]] ((rrel kind) a b)))
      (theorem! (str nm "_congr_rep")
        (t/forall [[a rep] [a' rep] [b rep] [b' rep]]
          (implies (rat/equiv a a') (rat/equiv b b') (t/app rep-rel a b) (t/app rep-rel a' b')))
        (t/lambda [[a rep] [a' rep] [b rep] [b' rep]
                   [ha (rat/equiv a a')] [hb (rat/equiv b b')] [h (t/app rep-rel a b)]]
          (rel-congr-proof kind a a' b b' ha hb h)))
      (define! nm (t/arrow Q (t/arrow Q t/prop))
        (lift2-prop rep-rel (c (str nm "_congr_rep")))))))

(defn- install-order-laws! []
  (let [x-of (fn [a b] (k/mul (rnum a) (rden b)))
        L (fn [rel a b] (rel-prop rel (leaf a) (leaf b)))]
    (q-theorem! "lt_irrefl" 1 (fn [[p]] (t/not' (lt p p)))
      (fn [[a]] (t/app (k/const "Int.lt_irrefl") (x-of a a))))
    (q-theorem! "le_refl" 1 (fn [[p]] (le p p))
      (fn [[a]] (t/app (k/const "Int.le_refl") (x-of a a))))
    (q-theorem! "le_of_lt" 2 (fn [[p q]] (implies (lt p q) (le p q)))
      (fn [[a b]] (t/lam "h" (L o/lt a b)
                         #(t/app (k/const "Int.le_of_lt") (x-of a b) (x-of b a) %))))
    ;; transitivity for each mix of < and ≤: scale both hypotheses, chain, cancel
    (doseq [[label r1 r2 out] [["lt_trans" :lt :lt :lt] ["le_trans" :le :le :le]
                               ["lt_of_lt_of_le" :lt :le :lt] ["lt_of_le_of_lt" :le :lt :lt]]]
      (q-theorem! label 3
        (fn [[p q s]] (implies ((if (= r1 :lt) lt le) p q) ((if (= r2 :lt) lt le) q s)
                               ((if (= out :lt) lt le) p s)))
        (fn [[a b s]]
          (let [mono1 (:mono (relations r1)) mono2 (:mono (relations r2))
                rel1 (:rel (relations r1)) rel2 (:rel (relations r2)) relo (:rel (relations out))]
            (t/lam "h1" (L rel1 a b)
                   (fn [h1]
                     (t/lam "h2" (L rel2 b s)
                            (fn [h2]
                              (let [f1 (mono1 (x-of a b) (x-of b a) (rden s) h1 (den-pos s))
                                    f2 (mono2 (x-of b s) (x-of s b) (rden a) h2 (den-pos a))
                                    x (x-of a s) y (x-of s a)
                                    g (o/by-omega (relo (k/mul x (rden b)) (k/mul y (rden b))) [f1 f2])]
                                (t/app (k/const (:cancel (relations out))) x y (rden b) (den-pos b) g))))))))))
    (q-theorem! "le_antisymm" 2 (fn [[p q]] (implies (le p q) (le q p) (k/eq-at Q l1 p q)))
      (fn [[a b]]
        (t/lam "h1" (L o/le a b)
               (fn [h1]
                 (t/lam "h2" (L o/le b a)
                        (fn [h2]
                          (sound a b (o/by-omega (k/eq (x-of a b) (x-of b a))
                                                 [[(L o/le a b) h1] [(L o/le b a) h2]]))))))))
    (q-theorem! "lt_trichotomy" 2
      (fn [[p q]] (t/or' (lt p q) (t/or' (k/eq-at Q l1 p q) (lt q p))))
      (fn [[a b]]
        (let [x (x-of a b) y (x-of b a)
              P (lt (mk a) (mk b)) E (k/eq-at Q l1 (mk a) (mk b)) R (lt (mk b) (mk a))
              goal (t/or' P (t/or' E R))]
          (t/or-elim (o/lt x y) (t/or' (k/eq x y) (o/lt y x)) goal
                     (t/app (k/const "Int.lt_trichotomy") x y)
                     (t/lam "h" (o/lt x y) #(t/or-inl P (t/or' E R) %))
                     (t/lam "h" (t/or' (k/eq x y) (o/lt y x))
                            (fn [h]
                              (t/or-inr P (t/or' E R)
                                        (t/or-elim (k/eq x y) (o/lt y x) (t/or' E R) h
                                                   (t/lam "e" (k/eq x y) #(t/or-inl E R (sound a b %)))
                                                   (t/lam "g" (o/lt y x) #(t/or-inr E R %))))))))))
    ;; monotonicity of addition: scale by (den s)² and let omega expand
    (doseq [[label kind] [["add_lt_add_left" :lt] ["add_le_add_left" :le]]]
      (q-theorem! label 3
        (fn [[p q s]] (let [rel (if (= kind :lt) lt le)] (implies (rel p q) (rel (add s p) (add s q)))))
        (fn [[a b s]]
          (let [{:keys [rel mono]} (relations kind)]
            (t/lam "h" (L rel a b)
                   (fn [h]
                     (let [ds (rden s)
                           f (mono (x-of a b) (x-of b a) (k/mul ds ds) h (int-mul-pos ds ds (den-pos s) (den-pos s)))]
                       (o/by-omega (rel-prop rel (radd (leaf s) (leaf a)) (radd (leaf s) (leaf b))) [f]))))))))
    ;; products of positives / nonnegatives
    (doseq [[label kind] [["mul_pos" :lt] ["mul_nonneg" :le]]]
      (q-theorem! label 2
        (fn [[p q]] (let [rel (if (= kind :lt) lt le)] (implies (rel zero p) (rel zero q) (rel zero (mul p q)))))
        (fn [[a b]]
          (let [rel (:rel (relations kind))
                za (rel-prop rel rzero (leaf a)) zb (rel-prop rel rzero (leaf b))]
            (t/lam "ha" za
                   (fn [ha]
                     (t/lam "hb" zb
                            (fn [hb]
                              (let [pa (o/by-omega (rel k/zero (rnum a)) [[za ha]])
                                    pb (o/by-omega (rel k/zero (rnum b)) [[zb hb]])
                                    prod (if (= kind :lt)
                                           [(o/lt k/zero (k/mul (rnum a) (rnum b))) (int-mul-pos (rnum a) (rnum b) pa pb)]
                                           [(o/le k/zero (k/mul (rnum a) (rnum b))) (o/mul-nonneg (rnum a) (rnum b) pa pb)])]
                                (o/by-omega (rel-prop rel rzero (rmul (leaf a) (leaf b))) [prod]))))))))))))

(defn- install-abs! []
  (define! "repAbs" (t/arrow rep rep)
    (t/lambda [[a rep]] (rat/make-rep (o/abs (rnum a)) (rden a) (den-pos a))))
  (theorem! "abs_congr_rep"
    (t/forall [[a rep] [a' rep]] (implies (rat/equiv a a') (rat/equiv (t/app (c "repAbs") a) (t/app (c "repAbs") a'))))
    (t/lambda [[a rep] [a' rep] [h (rat/equiv a a')]] (abs-congr-proof a a' h)))
  (define! "abs" (t/arrow Q Q) (lift1 (c "repAbs") (c "abs_congr_rep")))
  (q-theorem! "abs_nonneg" 1 (fn [[p]] (le zero (abs p)))
    (fn [[a]] (o/by-omega (rel-prop o/le rzero (rabs (leaf a)))
                          [[(o/le k/zero (o/abs (rnum a))) (t/app (k/const "Emmy.Analysis.Int.abs_nonneg") (rnum a))]])))
  (q-theorem! "abs_mul" 2 (fn [[p q]] (k/eq-at Q l1 (abs (mul p q)) (mul (abs p) (abs q))))
    (fn [[a b]]
      (let [x (rabs (rmul (leaf a) (leaf b)))
            y (rmul (rabs (leaf a)) (rabs (leaf b)))]
        (sound (:rep x) (:rep y)
               (:term (k/congr-mul (abs-mul-map (rnum a) (rnum b)) (k/refl (k/mul (rden a) (rden b)))))))))
  (q-theorem! "abs_triangle" 2 (fn [[p q]] (le (abs (add p q)) (add (abs p) (abs q))))
    (fn [[a b]]
      (let [na (rnum a) nb (rnum b) da (rden a) db (rden b)
            u (k/mul na db) v (k/mul nb da)
            tri [(o/le (o/abs (k/add u v)) (k/add (o/abs u) (o/abs v)))
                 (t/app (k/const "Emmy.Analysis.Int.abs_triangle") u v)]
            m1 (k/trans (abs-mul-map na db) (k/congr-mul (k/refl (o/abs na)) (abs-pos-map db (den-pos b))))
            m2 (k/trans (abs-mul-map nb da) (k/congr-mul (k/refl (o/abs nb)) (abs-pos-map da (den-pos a))))
            X (o/abs (k/add u v))
            Y (k/add (k/mul (o/abs na) db) (k/mul (o/abs nb) da))
            s1 (o/by-omega (o/le X Y) [tri [(k/eq (:lhs m1) (:rhs m1)) (:term m1)]
                                           [(k/eq (:lhs m2) (:rhs m2)) (:term m2)]])
            z (k/mul da db)
            mono [(o/le (k/mul z X) (k/mul z Y))
                  (t/app (k/const "Int.mul_le_mul_of_nonneg_left") X Y z s1
                         (t/app (k/const "Int.le_of_lt") k/zero z (int-mul-pos da db (den-pos a) (den-pos b))))]]
        (o/by-omega (rel-prop o/le (rabs (radd (leaf a) (leaf b))) (radd (rabs (leaf a)) (rabs (leaf b))))
                    [mono])))))

(defn- install-archimedean-and-half! []
  (define! "ofInt" (t/arrow k/int-type Q)
    (t/lambda [[m k/int-type]] (mk (rat/make-rep m k/one (t/app (k/const "Int.ofNat_succ_pos") (ansatz.kernel.expr/lit-nat 0))))))
  (q-theorem! "archimedean" 1
    (fn [[p]] (t/exists' k/int-type (t/lambda [[m k/int-type]] (lt p (of-int m)))))
    (fn [[a]]
      (let [na (rnum a) da (rden a)
            m (k/add (o/abs na) k/one)
            one-le [(o/le k/one da) (o/by-omega (o/le k/one da) [[(o/lt k/zero da) (den-pos a)]])]
            m-nonneg (o/by-omega (o/le k/zero m) [[(o/le k/zero (o/abs na)) (t/app (k/const "Emmy.Analysis.Int.abs_nonneg") na)]])
            mono [(o/le (k/mul m k/one) (k/mul m da))
                  (t/app (k/const "Int.mul_le_mul_of_nonneg_left") k/one da m (second one-le) m-nonneg)]
            proof (o/by-omega (o/lt (k/mul na k/one) (k/mul m da))
                              [mono [(o/le na (o/abs na)) (t/app (k/const "Emmy.Analysis.Int.le_abs") na)]])]
        (t/exists-intro k/int-type (t/lambda [[mm k/int-type]] (lt (mk a) (of-int mm))) m proof))))
  (define! "repHalf" rep (rat/make-rep k/one (k/lit 2) (t/app (k/const "Int.ofNat_succ_pos") (ansatz.kernel.expr/lit-nat 1))))
  (define! "half" Q (mk (c "repHalf")))
  (let [rhalf {:rep (c "repHalf") :num k/one :den (k/lit 2)}]
    (quot-law! "half_add_half" 1 #(add (mul half %) (mul half %)) identity
               #(radd (rmul rhalf %) (rmul rhalf %)) identity)
    (theorem! "half_pos" (lt zero half)
      (o/by-omega (rel-prop o/lt rzero rhalf) []))))

(defn inv [p] (t/app (c "inv") p))

(defn- eq-q [x y] (k/eq-at Q l1 x y))

(defn- install-field! []
  (let [rep-inv #(t/app (c "repInv") %)
        num0 #(k/eq (rnum %) k/zero)
        nonzero-rep (fn [a h]
                      (rat/make-rep (k/mul (rnum a) (rden a)) (k/mul (rnum a) (rnum a))
                                    (t/app (k/const "Emmy.Analysis.Int.mul_self_pos") (rnum a) h)))
        inst #(t/app (k/const "Int.decEq") (rnum %) k/zero)
        zero-branch (fn [a] (t/lam "h" (num0 a) (fn [_] (c "repZero"))))
        nonzero-branch (fn [a] (t/lam "h" (t/not' (num0 a)) #(nonzero-rep a %)))
        ;; inv a = repZero when num a = 0, and the nonzero representative otherwise
        dif (fn [pos? a h]
              (t/app (k/const (if pos? "dif_pos" "dif_neg") l1) (num0 a) (inst a) h rep
                     (zero-branch a) (nonzero-branch a)))
        ;; rewrite Equiv (inv a) (inv a') into Equiv x y given the two dif equations
        equiv-of-cases (fn [a a' x y ea ea' h]
                         (let [m1 (t/lambda [[z rep]] (rat/equiv z (rep-inv a')))
                               m2 (t/lambda [[z rep]] (rat/equiv x z))
                               step (t/transport-at rep l1 m2 y (rep-inv a')
                                                    (t/app (k/const "Eq.symm" l1) rep (rep-inv a') y ea') h)]
                           (t/transport-at rep l1 m1 x (rep-inv a)
                                           (t/app (k/const "Eq.symm" l1) rep (rep-inv a) x ea) step)))]
    (define! "repInv" (t/arrow rep rep)
      (t/lambda [[a rep]]
        (t/app (k/const "dite" l1) rep (num0 a) (inst a) (zero-branch a) (nonzero-branch a))))
    (theorem! "inv_congr_rep"
      (t/forall [[a rep] [a' rep]] (implies (rat/equiv a a') (rat/equiv (rep-inv a) (rep-inv a'))))
      (t/lambda [[a rep] [a' rep] [h (rat/equiv a a')]]
        (let [goal (rat/equiv (rep-inv a) (rep-inv a'))
              E {:lhs (k/mul (rnum a) (rden a')) :rhs (k/mul (rnum a') (rden a)) :term h}
              ;; num a = 0 forces num a' = 0 (and vice versa): cancel the positive denominator
              forces-zero (fn [b b' hz swap?]
                            (let [c (alg/linear-combination
                                     (k/mul (rnum b') (rden b)) (k/mul k/zero (rden b))
                                     [[(k/lit -1) (if swap? (k/symm E) E)]
                                      [(rden b') {:lhs (rnum b) :rhs k/zero :term hz}]])]
                              (t/app (r "int_mul_right_cancel") (rnum b') k/zero (rden b) (den-pos b) (:term c))))
              case-em (fn [x f-yes f-no]
                        (t/or-elim (num0 x) (t/not' (num0 x)) goal
                                   (t/decidable-em (num0 x) (inst x))
                                   (t/lam "hz" (num0 x) f-yes)
                                   (t/lam "hn" (t/not' (num0 x)) f-no)))]
          (case-em a
                   (fn [hz]
                     (case-em a'
                              (fn [hz']
                                (equiv-of-cases a a' (c "repZero") (c "repZero") (dif true a hz) (dif true a' hz')
                                                (t/app (r "equiv_refl") (c "repZero"))))
                              (fn [hn'] (t/absurd' (num0 a') goal (forces-zero a a' hz false) hn'))))
                   (fn [hn]
                     (case-em a'
                              (fn [hz'] (t/absurd' (num0 a) goal (forces-zero a' a hz' true) hn))
                              (fn [hn']
                                (let [x (nonzero-rep a hn) y (nonzero-rep a' hn')
                                      cross (alg/linear-combination
                                             (k/mul (k/mul (rnum a) (rden a)) (k/mul (rnum a') (rnum a')))
                                             (k/mul (k/mul (rnum a') (rden a')) (k/mul (rnum a) (rnum a)))
                                             [[(k/neg (k/mul (rnum a) (rnum a'))) E]])]
                                  (equiv-of-cases a a' x y (dif false a hn) (dif false a' hn') (:term cross))))))))))
    (define! "inv" (t/arrow Q Q) (lift1 (c "repInv") (c "inv_congr_rep")))
    (q-theorem! "mul_inv_cancel" 1
      (fn [[p]] (implies (t/not' (eq-q p zero)) (eq-q (mul p (inv p)) one)))
      (fn [[a]]
        (t/lam "hne" (t/not' (eq-q (mk a) zero))
               (fn [hne]
                 (let [hn (t/lam "h0" (num0 a)
                                 (fn [h0]
                                   (t/app hne (sound a (c "repZero")
                                                     (:term (alg/linear-combination
                                                             (k/mul (rnum a) k/one) (k/mul k/zero (rden a))
                                                             [[k/one {:lhs (rnum a) :rhs k/zero :term h0}]]))))))
                       v (nonzero-rep a hn)
                       e (dif false a hn)
                       step1 {:lhs (mk (t/app (r "mul") a (rep-inv a))) :rhs (mk (t/app (r "mul") a v))
                              :type Q :level l1
                              :term (t/app (k/const "congrArg" l1 l1) rep Q (rep-inv a) v
                                           (t/lambda [[z rep]] (mk (t/app (r "mul") a z))) e)}
                       vx {:rep v :num (k/mul (rnum a) (rden a)) :den (k/mul (rnum a) (rnum a))}
                       step2 {:lhs (mk (t/app (r "mul") a v)) :rhs one :type Q :level l1
                              :term (sound (t/app (r "mul") a v) (c "repOne")
                                           (equiv-proof (rmul (leaf a) vx) rone))}]
                   (:term (k/trans step1 step2)))))))
    (q-theorem! "inv_pos" 1
      (fn [[p]] (implies (lt zero p) (lt zero (inv p))))
      (fn [[a]]
        (let [hyp (rel-prop o/lt rzero (leaf a))
              motive (t/lambda [[z rep]] (rel-prop o/lt rzero (leaf z)))]
          (t/lam "h" hyp
                 (fn [h]
                   (t/or-elim (num0 a) (t/not' (num0 a)) (t/app motive (rep-inv a))
                              (t/decidable-em (num0 a) (inst a))
                              ;; num a = 0 contradicts 0 < a
                              (t/lam "hz" (num0 a)
                                     (fn [hz]
                                       (o/by-omega (rel-prop o/lt rzero (leaf (rep-inv a)))
                                                   [[hyp h] [(num0 a) hz]])))
                              ;; otherwise inv a = ⟨n·d, n·n⟩ with 0 < n·d
                              (t/lam "hn" (t/not' (num0 a))
                                     (fn [hn]
                                       (let [x (nonzero-rep a hn)
                                             na (rnum a) da (rden a)
                                             pn (o/by-omega (o/lt k/zero na) [[hyp h]])
                                             prod [(o/lt k/zero (k/mul na da)) (int-mul-pos na da pn (den-pos a))]
                                             px (o/by-omega (o/lt (k/mul k/zero (k/mul na na)) (k/mul (k/mul na da) k/one))
                                                            [prod])]
                                         (t/transport-at rep l1 motive x (rep-inv a)
                                                         (t/app (k/const "Eq.symm" l1) rep (rep-inv a) x (dif false a hn))
                                                         px))))))))))
    (let [lt-irrefl #(t/app (c "lt_irrefl") %)]
      (theorem! "ne_of_lt"
        (t/forall [[p Q] [q Q]] (implies (lt p q) (t/not' (eq-q p q))))
        (t/lambda [[p Q] [q Q] [h (lt p q)] [e (eq-q p q)]]
          ;; rewrite q to p in h : p < q, contradicting irreflexivity
          (t/app (lt-irrefl p)
                 (t/transport-at Q l1 (t/lambda [[z Q]] (lt p z)) q p
                                 (t/app (k/const "Eq.symm" l1) Q p q e) h))))
      (theorem! "zero_lt_one" (lt zero one) (o/by-omega (rel-prop o/lt rzero rone) []))
      (theorem! "zero_ne_one" (t/not' (eq-q zero one))
        (t/app (c "ne_of_lt") zero one (c "zero_lt_one"))))))

(defn- q-eq-map
  "Proof map for `h : x = y` in `Q`."
  [x y h]
  {:lhs x :rhs y :type Q :level l1 :term h})

(defn- congr-q
  "From `h : x = y` in `Q`, a proof map of `f x = f y` for `f : Q → Q`."
  [f x y h]
  (q-eq-map (t/app f x) (t/app f y)
            (t/app (k/const "congrArg" l1 l1) Q Q x y f h)))

(defn- rewrite-q
  "Proof of `motive y` from `h : motive x` and `e : x = y` in `Q`."
  [motive x y e h]
  (t/transport-at Q l1 (t/lambda [[z Q]] (motive z)) x y e h))

(defn- install-metric! []
  (quot-law! "sub_self" 1 #(sub % %) (constantly zero) #(radd % (rneg %)) (constantly rzero))
  (quot-law! "neg_sub" 2 #(neg (sub %1 %2)) #(sub %2 %1)
             #(rneg (radd %1 (rneg %2))) #(radd %2 (rneg %1)))
  (quot-law! "sub_add_sub" 3 #(add (sub %1 %2) (sub %2 %3)) #(sub %1 %3)
             #(radd (radd %1 (rneg %2)) (radd %2 (rneg %3))) #(radd %1 (rneg %3)))
  (quot-law! "add_sub_cancel" 2 #(add %2 (sub %1 %2)) (fn [p _] p)
             #(radd %2 (radd %1 (rneg %2))) (fn [a _] a))
  (theorem! "abs_zero" (eq-q (abs zero) zero)
    (sound (t/app (c "repAbs") (c "repZero")) (c "repZero")
           (o/with-abs-cases [k/zero] (k/eq (k/mul (o/abs k/zero) k/one) (k/mul k/zero k/one))
             #(o/by-omega (k/eq (k/mul (o/abs k/zero) k/one) (k/mul k/zero k/one)) %))))
  (q-theorem! "abs_neg" 1 (fn [[p]] (eq-q (abs (neg p)) (abs p)))
    (fn [[a]]
      (sound (t/app (c "repAbs") (t/app (r "neg") a)) (t/app (c "repAbs") a)
             (:term (k/congr-mul {:lhs (o/abs (k/neg (rnum a))) :rhs (o/abs (rnum a))
                                  :term (t/app (k/const "Emmy.Analysis.Int.abs_neg") (rnum a))}
                                 (k/refl (rden a)))))))
  (theorem! "abs_sub_comm"
    (t/forall [[p Q] [q Q]] (eq-q (abs (sub p q)) (abs (sub q p))))
    (t/lambda [[p Q] [q Q]]
      (:term (k/trans (q-eq-map (abs (sub p q)) (abs (neg (sub p q)))
                                (t/app (k/const "Eq.symm" l1) Q (abs (neg (sub p q))) (abs (sub p q))
                                       (t/app (c "abs_neg") (sub p q))))
                      (congr-q (c "abs") (neg (sub p q)) (sub q p) (t/app (c "neg_sub") p q))))))
  (theorem! "dist_triangle"
    (t/forall [[a Q] [b Q] [s Q]]
      (le (abs (sub a s)) (add (abs (sub a b)) (abs (sub b s)))))
    (t/lambda [[a Q] [b Q] [s Q]]
      (let [rhs (add (abs (sub a b)) (abs (sub b s)))]
        (rewrite-q #(le (abs %) rhs) (add (sub a b) (sub b s)) (sub a s)
                   (t/app (c "sub_add_sub") a b s)
                   (t/app (c "abs_triangle") (sub a b) (sub b s))))))
  (theorem! "add_lt_add"
    (t/forall [[x Q] [a Q] [y Q] [b Q]]
      (implies (lt x a) (lt y b) (lt (add x y) (add a b))))
    (t/lambda [[x Q] [a Q] [y Q] [b Q] [hx (lt x a)] [hy (lt y b)]]
      (let [h1 (t/app (c "add_lt_add_left") y b x hy)            ; x+y < x+b
            h2 (t/app (c "add_lt_add_left") x a b hx)            ; b+x < b+a
            h2' (rewrite-q #(lt % (add b a)) (add b x) (add x b) (t/app (c "add_comm") b x) h2)
            h2'' (rewrite-q #(lt (add x b) %) (add b a) (add a b) (t/app (c "add_comm") b a) h2')]
        (t/app (c "lt_trans") (add x y) (add x b) (add a b) h1 h2''))))
  (quot-law! "sub_add_add" 4 #(sub (add %1 %2) (add %3 %4)) #(add (sub %1 %3) (sub %2 %4))
             #(radd (radd %1 %2) (rneg (radd %3 %4))) #(radd (radd %1 (rneg %3)) (radd %2 (rneg %4))))
  (quot-law! "neg_sub_neg" 2 #(sub (neg %1) (neg %2)) #(neg (sub %1 %2))
             #(radd (rneg %1) (rneg (rneg %2))) #(rneg (radd %1 (rneg %2))))
  (theorem! "dist_add_le"
    (t/forall [[a Q] [b Q] [s Q] [u Q]]
      (le (abs (sub (add a b) (add s u))) (add (abs (sub a s)) (abs (sub b u)))))
    (t/lambda [[a Q] [b Q] [s Q] [u Q]]
      (let [rhs (add (abs (sub a s)) (abs (sub b u)))]
        (rewrite-q #(le (abs %) rhs) (add (sub a s) (sub b u)) (sub (add a b) (add s u))
                   (t/app (k/const "Eq.symm" l1) Q (sub (add a b) (add s u)) (add (sub a s) (sub b u))
                          (t/app (c "sub_add_add") a b s u))
                   (t/app (c "abs_triangle") (sub a s) (sub b u))))))
  (theorem! "dist_neg"
    (t/forall [[a Q] [b Q]] (eq-q (abs (sub (neg a) (neg b))) (abs (sub a b))))
    (t/lambda [[a Q] [b Q]]
      (:term (k/trans (congr-q (c "abs") (sub (neg a) (neg b)) (neg (sub a b)) (t/app (c "neg_sub_neg") a b))
                      (q-eq-map (abs (neg (sub a b))) (abs (sub a b)) (t/app (c "abs_neg") (sub a b)))))))
  (theorem! "half_pos_of_pos"
    (t/forall [[e Q]] (implies (lt zero e) (lt zero (mul half e))))
    (t/lambda [[e Q] [h (lt zero e)]]
      (t/app (c "mul_pos") half e (c "half_pos") h))))

;; ## Multiplication and order

(defn- eq-symm [x y e] (t/app (k/const "Eq.symm" l1) Q x y e))

(defn- install-mul-order! []
  (quot-law! "add_zero" 1 #(add % zero) identity #(radd % rzero) identity)
  ;; s·p REL s·q: scale the hypothesis by num s · den s
  (doseq [[label kind] [["mul_lt_mul_of_pos_left" :lt] ["mul_le_mul_of_nonneg_left" :le]]]
    (q-theorem! label 3
      (fn [[p q s]] (let [rel (if (= kind :lt) lt le)] (implies (rel p q) (rel zero s) (rel (mul s p) (mul s q)))))
      (fn [[a b s]]
        (let [rel (:rel (relations kind))
              hyp (rel-prop rel (leaf a) (leaf b))
              hs-prop (rel-prop rel rzero (leaf s))]
          (t/lam "h" hyp
                 (fn [h]
                   (t/lam "hs" hs-prop
                          (fn [hs]
                            (let [ns (rnum s) ds (rden s)
                                  x (k/mul (rnum a) (rden b)) y (k/mul (rnum b) (rden a))
                                  z (k/mul ns ds)
                                  pn (o/by-omega (rel k/zero ns) [[hs-prop hs]])
                                  f (if (= kind :lt)
                                      [(o/lt (k/mul z x) (k/mul z y))
                                       (t/app (k/const "Int.mul_lt_mul_of_pos_left") x y z h
                                              (int-mul-pos ns ds pn (den-pos s)))]
                                      [(o/le (k/mul z x) (k/mul z y))
                                       (t/app (k/const "Int.mul_le_mul_of_nonneg_left") x y z h
                                              (o/mul-nonneg ns ds pn (t/app (k/const "Int.le_of_lt") k/zero ds (den-pos s))))])]
                              (o/by-omega (rel-prop rel (rmul (leaf s) (leaf a)) (rmul (leaf s) (leaf b))) [f]))))))))))
  (theorem! "le_add_of_nonneg_right"
    (t/forall [[p Q] [s Q]] (implies (le zero s) (le p (add p s))))
    (t/lambda [[p Q] [s Q] [h (le zero s)]]
      (rewrite-q #(le % (add p s)) (add p zero) p (t/app (c "add_zero") p)
                 (t/app (c "add_le_add_left") zero s p h))))
  (theorem! "le_add_of_nonneg_left"
    (t/forall [[p Q] [s Q]] (implies (le zero s) (le p (add s p))))
    (t/lambda [[p Q] [s Q] [h (le zero s)]]
      (rewrite-q #(le p %) (add p s) (add s p) (t/app (c "add_comm") p s)
                 (t/app (c "le_add_of_nonneg_right") p s h))))
  (theorem! "lt_add_of_pos_right"
    (t/forall [[p Q] [s Q]] (implies (lt zero s) (lt p (add p s))))
    (t/lambda [[p Q] [s Q] [h (lt zero s)]]
      (rewrite-q #(lt % (add p s)) (add p zero) p (t/app (c "add_zero") p)
                 (t/app (c "add_lt_add_left") zero s p h))))
  (theorem! "lt_add_of_pos_left"
    (t/forall [[p Q] [s Q]] (implies (lt zero s) (lt p (add s p))))
    (t/lambda [[p Q] [s Q] [h (lt zero s)]]
      (rewrite-q #(lt p %) (add p s) (add s p) (t/app (c "add_comm") p s)
                 (t/app (c "lt_add_of_pos_right") p s h))))
  (theorem! "abs_le_add_dist"
    (t/forall [[a Q] [b Q]] (le (abs a) (add (abs b) (abs (sub a b)))))
    (t/lambda [[a Q] [b Q]]
      (rewrite-q #(le (abs %) (add (abs b) (abs (sub a b)))) (add b (sub a b)) a
                 (t/app (c "add_sub_cancel") a b)
                 (t/app (c "abs_triangle") b (sub a b)))))
  ;; a·c − b·d = a·(c − d) + d·(a − b)
  (quot-law! "mul_sub_mul" 4 #(sub (mul %1 %3) (mul %2 %4)) #(add (mul %1 (sub %3 %4)) (mul %4 (sub %1 %2)))
             #(radd (rmul %1 %3) (rneg (rmul %2 %4)))
             #(radd (rmul %1 (radd %3 (rneg %4))) (rmul %4 (radd %1 (rneg %2)))))
  (theorem! "dist_mul_le"
    (t/forall [[a Q] [b Q] [s Q] [u Q]]
      (le (abs (sub (mul a s) (mul b u))) (add (mul (abs a) (abs (sub s u))) (mul (abs u) (abs (sub a b))))))
    (t/lambda [[a Q] [b Q] [s Q] [u Q]]
      (let [x1 (mul a (sub s u)) x2 (mul u (sub a b))
            y1 (mul (abs a) (abs (sub s u))) y2 (mul (abs u) (abs (sub a b)))
            lhs (abs (sub (mul a s) (mul b u)))
            tri (rewrite-q #(le (abs %) (add (abs x1) (abs x2))) (add x1 x2) (sub (mul a s) (mul b u))
                           (eq-symm (sub (mul a s) (mul b u)) (add x1 x2) (t/app (c "mul_sub_mul") a b s u))
                           (t/app (c "abs_triangle") x1 x2))
            tri' (rewrite-q #(le lhs (add % (abs x2))) (abs x1) y1 (t/app (c "abs_mul") a (sub s u)) tri)]
        (rewrite-q #(le lhs (add y1 %)) (abs x2) y2 (t/app (c "abs_mul") u (sub a b)) tri'))))
  (theorem! "mul_lt_of_lt_of_lt"
    (t/forall [[x Q] [a Q] [y Q] [b Q]]
      (implies (le zero x) (lt x a) (le zero y) (lt y b) (lt (mul x y) (mul a b))))
    (t/lambda [[x Q] [a Q] [y Q] [b Q] [hx (le zero x)] [hxa (lt x a)] [hy (le zero y)] [hyb (lt y b)]]
      (let [h1 (t/app (c "mul_le_mul_of_nonneg_left") y b x (t/app (c "le_of_lt") y b hyb) hx)   ; x·y ≤ x·b
            hb (t/app (c "lt_of_le_of_lt") zero y b hy hyb)
            h2 (t/app (c "mul_lt_mul_of_pos_left") x a b hxa hb)                                ; b·x < b·a
            h2' (rewrite-q #(lt % (mul b a)) (mul b x) (mul x b) (t/app (c "mul_comm") b x) h2)
            h2'' (rewrite-q #(lt (mul x b) %) (mul b a) (mul a b) (t/app (c "mul_comm") b a) h2')]
        (t/app (c "lt_of_le_of_lt") (mul x y) (mul x b) (mul a b) h1 h2''))))
  (theorem! "mul_inv_mul"
    (t/forall [[a Q] [e Q]] (implies (lt zero a) (eq-q (mul a (mul (inv a) e)) e)))
    (t/lambda [[a Q] [e Q] [h (lt zero a)]]
      (let [ne (t/lam "h0" (eq-q a zero)
                      #(t/app (c "ne_of_lt") zero a h (eq-symm a zero %)))
            inv1 (t/app (c "mul_inv_cancel") a ne)]
        (:term (k/trans (q-eq-map (mul a (mul (inv a) e)) (mul (mul a (inv a)) e)
                                  (eq-symm (mul (mul a (inv a)) e) (mul a (mul (inv a) e))
                                           (t/app (c "mul_assoc") a (inv a) e)))
                        (q-eq-map (mul (mul a (inv a)) e) (mul one e)
                                  (t/app (k/const "congrArg" l1 l1) Q Q (mul a (inv a)) one
                                         (t/lambda [[z Q]] (mul z e)) inv1))
                        (q-eq-map (mul one e) e (t/app (c "one_mul") e))))))))

(defn- install-order-extras! []
  (q-theorem! "le_abs" 1 (fn [[p]] (le p (abs p)))
    (fn [[a]]
      (let [na (rnum a) da (rden a)
            mono [(o/le (k/mul da na) (k/mul da (o/abs na)))
                  (t/app (k/const "Int.mul_le_mul_of_nonneg_left") na (o/abs na) da
                         (t/app (k/const "Emmy.Analysis.Int.le_abs") na)
                         (t/app (k/const "Int.le_of_lt") k/zero da (den-pos a)))]]
        (o/by-omega (rel-prop o/le (leaf a) (rabs (leaf a))) [mono]))))
  (theorem! "add_lt_add_right"
    (t/forall [[p Q] [q Q] [s Q]] (implies (lt p q) (lt (add p s) (add q s))))
    (t/lambda [[p Q] [q Q] [s Q] [h (lt p q)]]
      (let [h1 (t/app (c "add_lt_add_left") p q s h)
            h2 (rewrite-q #(lt % (add s q)) (add s p) (add p s) (t/app (c "add_comm") s p) h1)]
        (rewrite-q #(lt (add p s) %) (add s q) (add q s) (t/app (c "add_comm") s q) h2))))
  (let [rhalf {:rep (c "repHalf") :num k/one :den (k/lit 2)}]
    (quot-law! "sub_half" 1 #(sub % (mul half %)) #(mul half %)
               #(radd % (rneg (rmul rhalf %))) #(rmul rhalf %)))
  (theorem! "add_pos"
    (t/forall [[p Q] [q Q]] (implies (lt zero p) (lt zero q) (lt zero (add p q))))
    (t/lambda [[p Q] [q Q] [hp (lt zero p)] [hq (lt zero q)]]
      (t/app (c "lt_trans") zero p (add p q) hp (t/app (c "lt_add_of_pos_right") p q hq))))
  (quot-law! "add_right_neg" 1 #(add % (neg %)) (constantly zero) #(radd % (rneg %)) (constantly rzero))
  (quot-law! "sub_add_cancel" 2 #(add (sub %1 %2) %2) (fn [p _] p)
             #(radd (radd %1 (rneg %2)) %2) (fn [a _] a))
  (quot-law! "add_sub_add_left" 3 #(sub (add %1 %2) (add %1 %3)) #(sub %2 %3)
             #(radd (radd %1 %2) (rneg (radd %1 %3))) #(radd %2 (rneg %3)))
  (theorem! "half_lt_self"
    (t/forall [[p Q]] (implies (lt zero p) (lt (mul half p) p)))
    (t/lambda [[p Q] [h (lt zero p)]]
      (let [hp (mul half p)]
        (rewrite-q #(lt hp %) (add hp hp) p (t/app (c "half_add_half") p)
                   (t/app (c "lt_add_of_pos_right") hp hp (t/app (c "half_pos_of_pos") p h))))))
  (theorem! "lt_of_sub_pos"
    (t/forall [[p Q] [q Q]] (implies (lt zero (sub q p)) (lt p q)))
    (t/lambda [[p Q] [q Q] [h (lt zero (sub q p))]]
      (let [h1 (t/app (c "add_lt_add_right") zero (sub q p) p h)
            h2 (rewrite-q #(lt % (add (sub q p) p)) (add zero p) p (t/app (c "zero_add") p) h1)]
        (rewrite-q #(lt p %) (add (sub q p) p) q (t/app (c "sub_add_cancel") q p) h2))))
  (theorem! "sub_pos_of_lt"
    (t/forall [[p Q] [q Q]] (implies (lt p q) (lt zero (sub q p))))
    (t/lambda [[p Q] [q Q] [h (lt p q)]]
      (rewrite-q #(lt % (sub q p)) (add p (neg p)) zero (t/app (c "add_right_neg") p)
                 (t/app (c "add_lt_add_right") p q (neg p) h))))
  (quot-law! "sub_zero" 1 #(sub % zero) identity #(radd % (rneg rzero)) identity)
  (quot-law! "add_sub_cancel_right" 2 #(sub (add %1 %2) %2) (fn [p _] p)
             #(radd (radd %1 %2) (rneg %2)) (fn [a _] a))
  (theorem! "lt_of_not_le"
    (t/forall [[p Q] [q Q]] (implies (t/not' (le q p)) (lt p q)))
    (t/lambda [[p Q] [q Q] [h (t/not' (le q p))]]
      (let [goal (lt p q)
            E (k/eq-at Q l1 p q)]
        (t/or-elim (lt p q) (t/or' E (lt q p)) goal
                   (t/app (c "lt_trichotomy") p q)
                   (t/lam "h1" (lt p q) identity)
                   (t/lam "h2" (t/or' E (lt q p))
                          (fn [h2]
                            (t/or-elim E (lt q p) goal h2
                                       (t/lam "e" E
                                              (fn [e]
                                                (t/absurd' (le q p) goal
                                                           (rewrite-q #(le % p) p q e (t/app (c "le_refl") p)) h)))
                                       (t/lam "g" (lt q p)
                                              #(t/absurd' (le q p) goal (t/app (c "le_of_lt") q p %) h)))))))))
  (q-theorem! "abs_of_pos" 1 (fn [[p]] (implies (lt zero p) (eq-q (abs p) p)))
    (fn [[a]]
      (let [hyp (rel-prop o/lt rzero (leaf a))]
        (t/lam "h" hyp
               (fn [h]
                 (let [pn (o/by-omega (o/lt k/zero (rnum a)) [[hyp h]])]
                   (sound (t/app (c "repAbs") a) a
                          (:term (k/congr-mul (abs-pos-map (rnum a) pn) (k/refl (rden a)))))))))))
  (theorem! "neg_pos_of_neg"
    (t/forall [[p Q]] (implies (lt p zero) (lt zero (neg p))))
    (t/lambda [[p Q] [h (lt p zero)]]
      (let [h1 (t/app (c "add_lt_add_right") p zero (neg p) h)
            h2 (rewrite-q #(lt % (add zero (neg p))) (add p (neg p)) zero (t/app (c "add_right_neg") p) h1)]
        (rewrite-q #(lt zero %) (add zero (neg p)) (neg p) (t/app (c "zero_add") (neg p)) h2))))
  (theorem! "neg_lt_neg"
    (t/forall [[p Q] [q Q]] (implies (lt p q) (lt (neg q) (neg p))))
    (t/lambda [[p Q] [q Q] [h (lt p q)]]
      (t/app (c "lt_of_sub_pos") (neg q) (neg p)
             (rewrite-q #(lt zero %) (sub q p) (sub (neg p) (neg q))
                        (t/app (k/const "Eq.symm" l1) Q (sub (neg p) (neg q)) (sub q p)
                               (t/app (k/const "Eq.trans" l1) Q (sub (neg p) (neg q)) (neg (sub p q)) (sub q p)
                                      (t/app (c "neg_sub_neg") p q) (t/app (c "neg_sub") p q)))
                        (t/app (c "sub_pos_of_lt") p q h)))))
  (theorem! "sub_lt_sub_left"
    (t/forall [[p Q] [q Q] [s Q]] (implies (lt p q) (lt (sub s q) (sub s p))))
    (t/lambda [[p Q] [q Q] [s Q] [h (lt p q)]]
      (t/app (c "add_lt_add_left") (neg q) (neg p) s (t/app (c "neg_lt_neg") p q h))))
  ;; |a − b| < d keeps b above a − d
  (theorem! "sub_lt_of_dist_lt"
    (t/forall [[a Q] [b Q] [d Q]] (implies (lt (abs (sub a b)) d) (lt (sub a d) b)))
    (t/lambda [[a Q] [b Q] [d Q] [h (lt (abs (sub a b)) d)]]
      (let [h1 (t/app (c "lt_of_le_of_lt") (sub a b) (abs (sub a b)) d (t/app (c "le_abs") (sub a b)) h)
            h2 (t/app (c "add_lt_add_right") (sub a b) d (sub b d) h1)
            h3 (rewrite-q #(lt % (add d (sub b d))) (add (sub a b) (sub b d)) (sub a d)
                          (t/app (c "sub_add_sub") a b d) h2)]
        (rewrite-q #(lt (sub a d) %) (add d (sub b d)) b (t/app (c "add_sub_cancel") b d) h3))))
  ;; e ≤ |x| and |x − y| < e/2 keep |y| above e/2
  (theorem! "half_lt_abs"
    (t/forall [[e Q] [x Q] [y Q]]
      (implies (le e (abs x)) (lt (abs (sub x y)) (mul half e)) (lt (mul half e) (abs y))))
    (t/lambda [[e Q] [x Q] [y Q] [hx (le e (abs x))] [hxy (lt (abs (sub x y)) (mul half e))]]
      (let [he (mul half e) ay (abs y) d (abs (sub x y))
            h1 (t/app (c "le_trans") e (abs x) (add ay d) hx (t/app (c "abs_le_add_dist") x y))
            h2 (t/app (c "lt_of_le_of_lt") e (add ay d) (add ay he) h1
                      (t/app (c "add_lt_add_left") d he ay hxy))
            h3 (t/app (c "add_lt_add_right") e (add ay he) (neg he) h2)
            h4 (rewrite-q #(lt % (add (add ay he) (neg he))) (sub e he) he (t/app (c "sub_half") e) h3)]
        (rewrite-q #(lt he %) (add (add ay he) (neg he)) ay (t/app (c "add_sub_cancel_right") ay he) h4))))
  ;; ε < a and |a − b| < ε/2 keep b above ε/2
  (theorem! "close_lower"
    (t/forall [[e Q] [a Q] [b Q]]
      (implies (lt e a) (lt (abs (sub a b)) (mul half e)) (lt (mul half e) b)))
    (t/lambda [[e Q] [a Q] [b Q] [hea (lt e a)] [hab (lt (abs (sub a b)) (mul half e))]]
      (let [he (mul half e)
            ;; a − b ≤ |a − b| < ε/2, so a − ε/2 < b
            h1 (t/app (c "lt_of_le_of_lt") (sub a b) (abs (sub a b)) he
                      (t/app (c "le_abs") (sub a b)) hab)
            h2 (t/app (c "add_lt_add_right") (sub a b) he (sub b he) h1)
            h3 (rewrite-q #(lt % (add he (sub b he))) (add (sub a b) (sub b he)) (sub a he)
                          (t/app (c "sub_add_sub") a b he) h2)
            h4 (rewrite-q #(lt (sub a he) %) (add he (sub b he)) b
                          (t/app (c "add_sub_cancel") b he) h3)
            ;; ε < a gives ε/2 = ε − ε/2 < a − ε/2
            h5 (t/app (c "add_lt_add_right") e a (neg he) hea)
            h6 (rewrite-q #(lt % (sub a he)) (sub e he) he (t/app (c "sub_half") e) h5)]
        (t/app (c "lt_trans") he (sub a he) b h6 h4)))))

;; ## Inverses

(defn- install-inv-laws! []
  (quot-law! "sub_mul" 3 #(mul (sub %1 %2) %3) #(sub (mul %1 %3) (mul %2 %3))
             #(rmul (radd %1 (rneg %2)) %3) #(radd (rmul %1 %3) (rneg (rmul %2 %3))))
  (quot-law! "left_distrib_sub" 3 #(mul %1 (sub %2 %3)) #(sub (mul %1 %2) (mul %1 %3))
             #(rmul %1 (radd %2 (rneg %3))) #(radd (rmul %1 %2) (rneg (rmul %1 %3))))
  (quot-law! "mul_left_comm" 3 #(mul %1 (mul %2 %3)) #(mul %2 (mul %1 %3))
             #(rmul %1 (rmul %2 %3)) #(rmul %2 (rmul %1 %3)))
  (quot-law! "mul_one" 1 #(mul % one) identity #(rmul % rone) identity)
  (doseq [[label op arg] [["mul_congr_fst" mul :fst] ["mul_congr_snd" mul :snd]
                          ["sub_congr_fst" sub :fst] ["sub_congr_snd" sub :snd]]]
    (theorem! label
      (t/forall [[a Q] [x Q] [y Q]]
        (implies (eq-q x y)
                 (if (= arg :fst) (eq-q (op x a) (op y a)) (eq-q (op a x) (op a y)))))
      (t/lambda [[a Q] [x Q] [y Q] [h (eq-q x y)]]
        (t/app (k/const "congrArg" l1 l1) Q Q x y
               (if (= arg :fst) (t/lambda [[z Q]] (op z a)) (t/lambda [[z Q]] (op a z))) h))))
  (theorem! "abs_congr"
    (t/forall [[x Q] [y Q]] (implies (eq-q x y) (eq-q (abs x) (abs y))))
    (t/lambda [[x Q] [y Q] [h (eq-q x y)]]
      (t/app (k/const "congrArg" l1 l1) Q Q x y (c "abs") h)))
  (let [step q-eq-map
        chain (fn [& maps] (:term (apply k/trans maps)))
        symm-q (fn [x y e] (t/app (k/const "Eq.symm" l1) Q x y e))
        ne-zero (fn [p] (t/not' (eq-q p zero)))]
    (theorem! "inv_mul_cancel"
      (t/forall [[p Q]] (implies (ne-zero p) (eq-q (mul (inv p) p) one)))
      (t/lambda [[p Q] [h (ne-zero p)]]
        (chain (step (mul (inv p) p) (mul p (inv p)) (t/app (c "mul_comm") (inv p) p))
               (step (mul p (inv p)) one (t/app (c "mul_inv_cancel") p h)))))
    ;; a⁻¹ is the unique b with a·b = 1
    (theorem! "inv_eq_of_mul_eq_one"
      (t/forall [[p Q] [q Q]] (implies (ne-zero p) (eq-q (mul p q) one) (eq-q (inv p) q)))
      (t/lambda [[p Q] [q Q] [hne (ne-zero p)] [h (eq-q (mul p q) one)]]
        (let [ip (inv p)]
          (chain (step ip (mul ip one) (symm-q (mul ip one) ip (t/app (c "mul_one") ip)))
                 (step (mul ip one) (mul ip (mul p q))
                       (t/app (c "mul_congr_snd") ip one (mul p q)
                              (symm-q (mul p q) one h)))
                 (step (mul ip (mul p q)) (mul (mul ip p) q)
                       (symm-q (mul (mul ip p) q) (mul ip (mul p q)) (t/app (c "mul_assoc") ip p q)))
                 (step (mul (mul ip p) q) (mul one q)
                       (t/app (c "mul_congr_fst") q (mul ip p) one
                                     (t/app (c "inv_mul_cancel") p hne)))
                 (step (mul one q) q (t/app (c "one_mul") q))))))
    (theorem! "inv_zero" (eq-q (inv zero) zero)
      (let [a (c "repZero")
            e (t/app (k/const "dif_pos" l1) (k/eq (rnum a) k/zero) (t/app (k/const "Int.decEq") (rnum a) k/zero)
                     (t/app (k/const "Eq.refl" l1) k/int-type k/zero) rep
                     (t/lam "h" (k/eq (rnum a) k/zero) (fn [_] (c "repZero")))
                     (t/lam "h" (t/not' (k/eq (rnum a) k/zero))
                            #(rat/make-rep (k/mul (rnum a) (rden a)) (k/mul (rnum a) (rnum a))
                                           (t/app (k/const "Emmy.Analysis.Int.mul_self_pos") (rnum a) %))))]
        (t/app (k/const "congrArg" l1 l1) rep Q (t/app (c "repInv") a) a
               (t/lambda [[z rep]] (mk z)) e)))
    (theorem! "abs_one" (eq-q (abs one) one)
      (sound (t/app (c "repAbs") (c "repOne")) (c "repOne")
             (o/with-abs-cases [k/one] (k/eq (k/mul (o/abs k/one) k/one) (k/mul k/one k/one))
               #(o/by-omega (k/eq (k/mul (o/abs k/one) k/one) (k/mul k/one k/one)) %))))
    (theorem! "abs_of_neg"
      (t/forall [[p Q]] (implies (lt p zero) (eq-q (abs p) (neg p))))
      (t/lambda [[p Q] [h (lt p zero)]]
        (chain (step (abs p) (abs (neg p)) (symm-q (abs (neg p)) (abs p) (t/app (c "abs_neg") p)))
               (step (abs (neg p)) (neg p) (t/app (c "abs_of_pos") (neg p) (t/app (c "neg_pos_of_neg") p h))))))
    (theorem! "abs_pos_of_ne_zero"
      (t/forall [[p Q]] (implies (ne-zero p) (lt zero (abs p))))
      (t/lambda [[p Q] [hne (ne-zero p)]]
        (let [goal (lt zero (abs p))
              E (eq-q p zero)]
          (t/or-elim (lt p zero) (t/or' E (lt zero p)) goal
                     (t/app (c "lt_trichotomy") p zero)
                     (t/lam "hneg" (lt p zero)
                            (fn [hneg]
                              (rewrite-q #(lt zero %) (neg p) (abs p)
                                         (symm-q (abs p) (neg p) (t/app (c "abs_of_neg") p hneg))
                                         (t/app (c "neg_pos_of_neg") p hneg))))
                     (t/lam "hrest" (t/or' E (lt zero p))
                            (fn [hrest]
                              (t/or-elim E (lt zero p) goal hrest
                                         (t/lam "he" E #(t/absurd' E goal % hne))
                                         (t/lam "hpos" (lt zero p)
                                                (fn [hpos]
                                                  (rewrite-q #(lt zero %) p (abs p)
                                                             (symm-q (abs p) p (t/app (c "abs_of_pos") p hpos))
                                                             hpos))))))))))
    (theorem! "abs_inv"
      (t/forall [[p Q]] (implies (ne-zero p) (eq-q (abs (inv p)) (inv (abs p)))))
      (t/lambda [[p Q] [hne (ne-zero p)]]
        (let [ap (abs p)
              ap-ne (t/lam "h0" (eq-q ap zero)
                           #(t/app (c "ne_of_lt") zero ap (t/app (c "abs_pos_of_ne_zero") p hne)
                                   (symm-q ap zero %)))
              prod (chain (step (mul ap (abs (inv p))) (abs (mul p (inv p)))
                                (symm-q (abs (mul p (inv p))) (mul ap (abs (inv p)))
                                        (t/app (c "abs_mul") p (inv p))))
                          (step (abs (mul p (inv p))) (abs one)
                                (t/app (k/const "congrArg" l1 l1) Q Q (mul p (inv p)) one (c "abs")
                                       (t/app (c "mul_inv_cancel") p hne)))
                          (step (abs one) one (c "abs_one")))]
          (symm-q (inv ap) (abs (inv p))
                  (t/app (c "inv_eq_of_mul_eq_one") ap (abs (inv p)) ap-ne prod)))))
    ;; inverses reverse strict order on positives
    (theorem! "inv_lt_inv_of_lt"
      (t/forall [[p Q] [q Q]] (implies (lt zero p) (lt p q) (lt (inv q) (inv p))))
      (t/lambda [[p Q] [q Q] [hp (lt zero p)] [h (lt p q)]]
        (let [ip (inv p) iq (inv q)
              hq (t/app (c "lt_trans") zero p q hp h)
              hip (t/app (c "inv_pos") p hp) hiq (t/app (c "inv_pos") q hq)
              k (mul ip iq)
              hk (t/app (c "mul_pos") ip iq hip hiq)
              p-ne (t/lam "h0" (eq-q p zero) #(t/app (c "ne_of_lt") zero p hp (symm-q p zero %)))
              q-ne (t/lam "h0" (eq-q q zero) #(t/app (c "ne_of_lt") zero q hq (symm-q q zero %)))
              ;; k·p = q⁻¹ and k·q = p⁻¹
              kp (chain (step (mul k p) (mul (mul iq ip) p)
                             (t/app (c "mul_congr_fst") p k (mul iq ip)
                                     (t/app (c "mul_comm") ip iq)))
                        (step (mul (mul iq ip) p) (mul iq (mul ip p)) (t/app (c "mul_assoc") iq ip p))
                        (step (mul iq (mul ip p)) (mul iq one)
                              (t/app (c "mul_congr_snd") iq (mul ip p) one
                                     (t/app (c "inv_mul_cancel") p p-ne)))
                        (step (mul iq one) iq (t/app (c "mul_one") iq)))
              kq (chain (step (mul k q) (mul ip (mul iq q)) (t/app (c "mul_assoc") ip iq q))
                        (step (mul ip (mul iq q)) (mul ip one)
                              (t/app (c "mul_congr_snd") ip (mul iq q) one
                                     (t/app (c "inv_mul_cancel") q q-ne)))
                        (step (mul ip one) ip (t/app (c "mul_one") ip)))
              scaled (t/app (c "mul_lt_mul_of_pos_left") p q k h hk)]
          (rewrite-q #(lt % ip) (mul k p) iq kp
                     (rewrite-q #(lt (mul k p) %) (mul k q) ip kq scaled)))))
    ;; a⁻¹ − b⁻¹ = a⁻¹·(b⁻¹·(b − a))
    (theorem! "inv_sub_inv"
      (t/forall [[p Q] [q Q]]
        (implies (ne-zero p) (ne-zero q)
                 (eq-q (sub (inv p) (inv q)) (mul (inv p) (mul (inv q) (sub q p))))))
      (t/lambda [[p Q] [q Q] [hp (ne-zero p)] [hq (ne-zero q)]]
        (let [ip (inv p) iq (inv q)
              ;; q⁻¹·(q·p⁻¹) = p⁻¹ and q⁻¹·(p·p⁻¹) = q⁻¹
              e1 (chain (step (mul iq (mul q ip)) (mul q (mul iq ip)) (t/app (c "mul_left_comm") iq q ip))
                        (step (mul q (mul iq ip)) (mul (mul q iq) ip)
                              (symm-q (mul (mul q iq) ip) (mul q (mul iq ip)) (t/app (c "mul_assoc") q iq ip)))
                        (step (mul (mul q iq) ip) (mul one ip)
                              (t/app (c "mul_congr_fst") ip (mul q iq) one (t/app (c "mul_inv_cancel") q hq)))
                        (step (mul one ip) ip (t/app (c "one_mul") ip)))
              e2 (chain (step (mul iq (mul p ip)) (mul p (mul iq ip)) (t/app (c "mul_left_comm") iq p ip))
                        (step (mul p (mul iq ip)) (mul p (mul ip iq))
                              (t/app (c "mul_congr_snd") p (mul iq ip) (mul ip iq) (t/app (c "mul_comm") iq ip)))
                        (step (mul p (mul ip iq)) (mul (mul p ip) iq)
                              (symm-q (mul (mul p ip) iq) (mul p (mul ip iq)) (t/app (c "mul_assoc") p ip iq)))
                        (step (mul (mul p ip) iq) (mul one iq)
                              (t/app (c "mul_congr_fst") iq (mul p ip) one (t/app (c "mul_inv_cancel") p hp)))
                        (step (mul one iq) iq (t/app (c "one_mul") iq)))]
          (symm-q (mul ip (mul iq (sub q p))) (sub ip iq)
                  (chain (step (mul ip (mul iq (sub q p))) (mul iq (mul ip (sub q p)))
                               (t/app (c "mul_left_comm") ip iq (sub q p)))
                         (step (mul iq (mul ip (sub q p))) (mul iq (sub (mul q ip) (mul p ip)))
                               (t/app (c "mul_congr_snd") iq (mul ip (sub q p)) (sub (mul q ip) (mul p ip))
                                      (chain (step (mul ip (sub q p)) (mul (sub q p) ip)
                                                   (t/app (c "mul_comm") ip (sub q p)))
                                             (step (mul (sub q p) ip) (sub (mul q ip) (mul p ip))
                                                   (t/app (c "sub_mul") q p ip)))))
                         (step (mul iq (sub (mul q ip) (mul p ip)))
                               (sub (mul iq (mul q ip)) (mul iq (mul p ip)))
                               (t/app (c "left_distrib_sub") iq (mul q ip) (mul p ip)))
                         (step (sub (mul iq (mul q ip)) (mul iq (mul p ip))) (sub ip (mul iq (mul p ip)))
                               (t/app (c "sub_congr_fst") (mul iq (mul p ip)) (mul iq (mul q ip)) ip e1))
                         (step (sub ip (mul iq (mul p ip))) (sub ip iq)
                               (t/app (c "sub_congr_snd") ip (mul iq (mul p ip)) iq e2)))))))
    (theorem! "inv_mul_mul"
      (t/forall [[p Q] [e Q]] (implies (lt zero p) (eq-q (mul (inv p) (mul p e)) e)))
      (t/lambda [[p Q] [e Q] [h (lt zero p)]]
        (let [ip (inv p)
              p-ne (t/lam "h0" (eq-q p zero) #(t/app (c "ne_of_lt") zero p h (symm-q p zero %)))]
          (chain (step (mul ip (mul p e)) (mul (mul ip p) e)
                       (symm-q (mul (mul ip p) e) (mul ip (mul p e)) (t/app (c "mul_assoc") ip p e)))
                 (step (mul (mul ip p) e) (mul one e)
                       (t/app (c "mul_congr_fst") e (mul ip p) one
                                     (t/app (c "inv_mul_cancel") p p-ne)))
                 (step (mul one e) e (t/app (c "one_mul") e))))))
    (theorem! "ne_zero_of_lt_abs"
      (t/forall [[d Q] [p Q]] (implies (lt zero d) (lt d (abs p)) (ne-zero p)))
      (t/lambda [[d Q] [p Q] [hd (lt zero d)] [h (lt d (abs p))] [h0 (eq-q p zero)]]
        (t/app (c "lt_irrefl") d
               (t/app (c "lt_trans") d zero d
                      (rewrite-q #(lt d %) (abs p) zero
                                 (chain (step (abs p) (abs zero) (t/app (c "abs_congr") p zero h0))
                                        (step (abs zero) zero (c "abs_zero")))
                                 h)
                      hd))))
    ;; |a⁻¹| < d⁻¹ whenever 0 < d < |a|
    (theorem! "abs_inv_lt"
      (t/forall [[d Q] [p Q]] (implies (lt zero d) (lt d (abs p)) (lt (abs (inv p)) (inv d))))
      (t/lambda [[d Q] [p Q] [hd (lt zero d)] [h (lt d (abs p))]]
        (let [p-ne (t/lam "h0" (eq-q p zero)
                          (fn [h0]
                            (t/app (c "lt_irrefl") d
                                   (t/app (c "lt_trans") d zero d
                                          (rewrite-q #(lt d %) (abs p) zero
                                                     (chain (step (abs p) (abs zero)
                                                                  (t/app (k/const "congrArg" l1 l1) Q Q p zero (c "abs") h0))
                                                            (step (abs zero) zero (c "abs_zero")))
                                                     h)
                                          hd))))]
          (rewrite-q #(lt % (inv d)) (inv (abs p)) (abs (inv p))
                     (symm-q (abs (inv p)) (inv (abs p)) (t/app (c "abs_inv") p p-ne))
                     (t/app (c "inv_lt_inv_of_lt") d (abs p) hd h)))))))

(defn- install-inv-estimate! []
  (let [step q-eq-map
        chain (fn [& maps] (:term (apply k/trans maps)))
        symm-q (fn [x y e] (t/app (k/const "Eq.symm" l1) Q x y e))]
    ;; the Cauchy estimate for inverses: |a⁻¹ − b⁻¹| = |a⁻¹|·(|b⁻¹|·|b − a|) < e
    (theorem! "dist_inv_lt"
      (t/forall [[d Q] [a Q] [b Q] [e Q]]
        (implies (lt zero d) (lt d (abs a)) (lt d (abs b)) (lt (abs (sub a b)) (mul d (mul d e)))
                 (lt (abs (sub (inv a) (inv b))) e)))
      (t/lambda [[d Q] [a Q] [b Q] [e Q]
                 [hd (lt zero d)] [ha (lt d (abs a))] [hb (lt d (abs b))]
                 [hab (lt (abs (sub a b)) (mul d (mul d e)))]]
        (let [ia (inv a) ib (inv b) id (inv d)
              aa (abs ia) ab (abs ib) ba (abs (sub b a))
              a-ne (t/app (c "ne_zero_of_lt_abs") d a hd ha)
              b-ne (t/app (c "ne_zero_of_lt_abs") d b hd hb)
              ;; |a⁻¹ − b⁻¹| = |a⁻¹|·(|b⁻¹|·|b − a|)
              eq1 (chain (step (abs (sub ia ib)) (abs (mul ia (mul ib (sub b a))))
                               (t/app (c "abs_congr") (sub ia ib) (mul ia (mul ib (sub b a)))
                                      (t/app (c "inv_sub_inv") a b a-ne b-ne)))
                         (step (abs (mul ia (mul ib (sub b a)))) (mul aa (abs (mul ib (sub b a))))
                               (t/app (c "abs_mul") ia (mul ib (sub b a))))
                         (step (mul aa (abs (mul ib (sub b a)))) (mul aa (mul ab ba))
                               (t/app (c "mul_congr_snd") aa (abs (mul ib (sub b a))) (mul ab ba)
                                      (t/app (c "abs_mul") ib (sub b a)))))
              hba (rewrite-q #(lt % (mul d (mul d e))) (abs (sub a b)) ba
                             (t/app (c "abs_sub_comm") a b) hab)
              h2 (t/app (c "mul_lt_of_lt_of_lt") ab id ba (mul d (mul d e))
                        (t/app (c "abs_nonneg") ib) (t/app (c "abs_inv_lt") d b hd hb)
                        (t/app (c "abs_nonneg") (sub b a)) hba)
              h2' (rewrite-q #(lt (mul ab ba) %) (mul id (mul d (mul d e))) (mul d e)
                             (t/app (c "inv_mul_mul") d (mul d e) hd) h2)
              h3 (t/app (c "mul_lt_of_lt_of_lt") aa id (mul ab ba) (mul d e)
                        (t/app (c "abs_nonneg") ia) (t/app (c "abs_inv_lt") d a hd ha)
                        (t/app (c "mul_nonneg") ab ba (t/app (c "abs_nonneg") ib) (t/app (c "abs_nonneg") (sub b a)))
                        h2')
              h3' (rewrite-q #(lt (mul aa (mul ab ba)) %) (mul id (mul d e)) e
                             (t/app (c "inv_mul_mul") d e hd) h3)]
          (rewrite-q #(lt % e) (mul aa (mul ab ba)) (abs (sub ia ib))
                     (symm-q (abs (sub ia ib)) (mul aa (mul ab ba)) eq1)
                     h3'))))))

(defn install!
  "Installs ℚ as an ordered commutative ring with absolute value, the
  Archimedean property and halving. Idempotent."
  []
  (rat/install!)
  (o/install!)
  (locking k/install-lock
    (define! "repZero" rep (rat/make-rep k/zero k/one (t/app (k/const "Int.ofNat_succ_pos") (ansatz.kernel.expr/lit-nat 0))))
    (define! "repOne" rep (rat/make-rep k/one k/one (t/app (k/const "Int.ofNat_succ_pos") (ansatz.kernel.expr/lit-nat 0))))
    (define! "Q" t/type0 (t/quot-type rep equiv-rel))
    (define! "zero" Q (mk (c "repZero")))
    (define! "one" Q (mk (c "repOne")))
    (define! "add" (t/arrow Q (t/arrow Q Q)) (lift2 (r "add") (r "add_congr")))
    (define! "mul" (t/arrow Q (t/arrow Q Q)) (lift2 (r "mul") (r "mul_congr")))
    (define! "neg" (t/arrow Q Q) (lift1 (r "neg") (r "neg_congr")))
    (define! "sub" (t/arrow Q (t/arrow Q Q)) (lams ["p" "q"] Q (fn [[p q]] (add p (neg q)))))

    (quot-law! "add_comm" 2 add #(add %2 %1) radd #(radd %2 %1))
    (quot-law! "add_assoc" 3 #(add (add %1 %2) %3) #(add %1 (add %2 %3))
               #(radd (radd %1 %2) %3) #(radd %1 (radd %2 %3)))
    (quot-law! "zero_add" 1 #(add zero %) identity #(radd rzero %) identity)
    (quot-law! "add_left_neg" 1 #(add (neg %) %) (constantly zero) #(radd (rneg %) %) (constantly rzero))
    (quot-law! "mul_comm" 2 mul #(mul %2 %1) rmul #(rmul %2 %1))
    (quot-law! "mul_assoc" 3 #(mul (mul %1 %2) %3) #(mul %1 (mul %2 %3))
               #(rmul (rmul %1 %2) %3) #(rmul %1 (rmul %2 %3)))
    (quot-law! "one_mul" 1 #(mul one %) identity #(rmul rone %) identity)
    (quot-law! "left_distrib" 3 #(mul %1 (add %2 %3)) #(add (mul %1 %2) (mul %1 %3))
               #(rmul %1 (radd %2 %3)) #(radd (rmul %1 %2) (rmul %1 %3)))
    (install-order!)
    (install-order-laws!)
    (install-abs!)
    (install-archimedean-and-half!)
    (install-field!)
    (install-metric!)
    (install-mul-order!)
    (install-order-extras!)
    (install-inv-laws!)
    (install-inv-estimate!))
  :installed)
