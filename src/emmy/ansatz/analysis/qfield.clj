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
    (install-metric!))
  :installed)
