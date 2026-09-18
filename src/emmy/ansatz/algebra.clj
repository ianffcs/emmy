#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.algebra
  "Proof-producing commutative-ring normalization over `Int`: the `int_ring`
  tactic for Ansatz.

  `int_ring` closes goals `lhs = rhs` in `Int` that hold as polynomial
  identities. Any subterm that isn't `+`, `-`, `*`, negation or an integer
  literal is treated as an opaque atom, so it also proves goals like

  ```
  peval x a * peval x b + h * (peval x a) = peval x a * (h + peval x b)
  ```

  which is what the induction steps of [[emmy.ansatz.calculus]] need.

  `(int_ring [r₁ r₂ …])` first rewrites both sides bottom-up with the
  equations `rᵢ`, like `simp only [r₁ r₂ …]; ring` in Lean. Each `rᵢ` names
  either a global theorem `∀ xs, lhs = rhs` (e.g. an equation lemma
  `peval_add`), a hypothesis `h : lhs = rhs` (e.g. an induction hypothesis),
  or a definition `f`, in which case applications of `f` are unfolded to weak
  head normal form (justified by `Eq.refl`, i.e. by the kernel's definitional
  equality). Unfolding suits non-recursive definitions whose arguments are
  constructors, such as a `match` after `cases`.

  `(int_ring_split [r₁ r₂ …])` is `int_ring` preceded by automatic case
  splitting, like Lean's `split`: while some application of a definition among
  the `rᵢ` is stuck on a local variable (its unfolding reaches a `casesOn` or
  `rec` of that variable), it runs `cases` on the variable, then closes every
  resulting goal with `int_ring`.
  Rewriting reaches arguments of any non-dependent application through
  `congrArg`/`congr`, so it works under definitions and on non-`Int` subterms.

  Both sides are brought to a canonical sum of monomials

  ```
  c₁ * (a * (b * 1)) + (c₂ * (a * 1) + (… + 0))
  ```

  (terms sorted by monomial, atoms within a monomial sorted by index, integer
  coefficients `cᵢ ≠ 0`). Every rewrite step is an instantiated `Init` lemma
  (`Int.add_assoc`, `Int.mul_left_comm`, `Int.add_mul`, …) and every coefficient
  computation is `Eq.refl` checked by kernel evaluation, so the resulting
  proof term relies on nothing but the kernel and Lean's `Init`. The
  reification in this namespace is *not* trusted: if it misreads a term, the
  kernel rejects the proof.

  This exists because Ansatz 0.2.84's own `ring` can't certify non-ground
  goals, and its `grind` ring solver is a stub."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [ansatz.kernel.tc :as tc]
            [ansatz.tactic.basic :as basic]
            [ansatz.tactic.proof :as proof]
            [emmy.ansatz.core :as k]))

;; ## Reification
;;
;; Kernel terms become a small IR over atoms:
;;
;;   [:lit n] [:atom i] [:add a b] [:sub a b] [:mul a b] [:neg a]
;;
;; `ctx` maps atom expressions to indices (in order of first appearance) and
;; back.

(def ^:private empty-ctx {:index {} :atoms []})

(defn- intern-atom [ctx expr]
  (if-let [i (get-in ctx [:index expr])]
    [ctx i]
    (let [i (count (:atoms ctx))]
      [(-> ctx
           (assoc-in [:index expr] i)
           (update :atoms conj expr))
       i])))

(defn- app-view
  "`[head-name args]` for an application of a constant, else nil."
  [expr]
  (let [[head args] (e/get-app-fn-args expr)]
    (when (e/const? head)
      [(name/->string (e/const-name head)) (vec args)])))

(defn- nat-value
  "Value of a closed `Nat` numeral: a raw literal, `OfNat.ofNat Nat n _`,
  `Nat.zero` or `Nat.succ` of a numeral."
  [expr]
  (cond
    (e/lit-nat? expr) (bigint (e/lit-nat-val expr))
    (and (e/const? expr) (= "Nat.zero" (name/->string (e/const-name expr)))) 0N
    :else
    (when-let [[head args] (app-view expr)]
      (case head
        "OfNat.ofNat" (let [n (get args 1)]
                        (when (and (= 3 (count args)) (e/lit-nat? n))
                          (bigint (e/lit-nat-val n))))
        "Nat.succ" (when (= 1 (count args))
                     (some-> (nat-value (args 0)) inc))
        nil))))

(defn- int-type? [expr]
  (= expr k/int-type))

(defn- classify
  "Returns `[op args]` for an arithmetic `Int` term, `[:lit n]` for a literal,
  or nil for an atom."
  [expr]
  (when-let [[head args] (app-view expr)]
    (let [n (count args)]
      (case head
        "Int.add" (when (= n 2) [:add args])
        "Int.mul" (when (= n 2) [:mul args])
        "Int.sub" (when (= n 2) [:sub args])
        "Int.neg" (when (= n 1) [:neg args])
        "HAdd.hAdd" (when (and (= n 6) (int-type? (args 0))) [:add (subvec args 4)])
        "HMul.hMul" (when (and (= n 6) (int-type? (args 0))) [:mul (subvec args 4)])
        "HSub.hSub" (when (and (= n 6) (int-type? (args 0))) [:sub (subvec args 4)])
        "Neg.neg" (when (and (= n 3) (int-type? (args 0))) [:neg (subvec args 2)])
        "OfNat.ofNat" (when (and (= n 3) (int-type? (args 0)) (e/lit-nat? (args 1)))
                        [:lit (bigint (e/lit-nat-val (args 1)))])
        "Int.ofNat" (when-let [v (and (= n 1) (nat-value (args 0)))]
                      [:lit v])
        "Int.negSucc" (when-let [v (and (= n 1) (nat-value (args 0)))]
                        [:lit (- (inc v))])
        nil))))

(defn- reify-term [ctx expr]
  (if-let [[op args] (classify expr)]
    (if (= op :lit)
      [ctx [:lit args]]
      (let [[ctx irs] (reduce (fn [[ctx acc] arg]
                                (let [[ctx ir] (reify-term ctx arg)]
                                  [ctx (conj acc ir)]))
                              [ctx []]
                              args)]
        [ctx (into [op] irs)]))
    (let [[ctx i] (intern-atom ctx expr)]
      [ctx [:atom i]])))

;; ## Normal forms
;;
;; A polynomial is a vector of `[coeff monomial]`, sorted by monomial; a
;; monomial is a sorted vector of atom indices (with repetition).

(defn- mon-expr [ctx mon]
  (if (empty? mon)
    k/one
    (k/mul (get-in ctx [:atoms (first mon)])
           (mon-expr ctx (subvec mon 1)))))

(defn- term-expr [ctx [c mon]]
  (k/mul (k/lit c) (mon-expr ctx mon)))

(defn- poly-expr [ctx poly]
  (if (empty? poly)
    k/zero
    (k/add (term-expr ctx (first poly))
           (poly-expr ctx (subvec poly 1)))))

(defn- ground
  "Proof that `op c1 c2` equals its value, checked by kernel evaluation."
  [op c1 c2]
  (let [v (case op :add (+ c1 c2) :mul (* c1 c2))]
    {:lhs  ((case op :add k/add :mul k/mul) (k/lit c1) (k/lit c2))
     :rhs  (k/lit v)
     :term (:term (k/refl (k/lit v)))}))

(defn- with-rhs
  "Restates `p`'s right side as `rhs`, which must be definitionally equal to
  it. Keeps later lemma instantiations syntactically aligned with the
  canonical spelling; the kernel re-checks the claim."
  [p rhs]
  (assoc p :rhs rhs))

(defn- mmul
  "Proof of `M₁ * M₂ = M` for monomials `m1`, `m2`. Returns `[mon proof]`."
  [ctx m1 m2]
  (cond
    (empty? m1) [m2 (k/lemma "Int.one_mul" (mon-expr ctx m2))]
    (empty? m2) [m1 (k/lemma "Int.mul_one" (mon-expr ctx m1))]
    :else
    (let [v (first m1) w (first m2)]
      (if (<= v w)
        (let [atom (get-in ctx [:atoms v])
              [m p] (mmul ctx (subvec m1 1) m2)]
          [(into [v] m)
           (k/trans (k/lemma "Int.mul_assoc" atom (mon-expr ctx (subvec m1 1)) (mon-expr ctx m2))
                    (k/congr-mul (k/refl atom) p))])
        (let [atom (get-in ctx [:atoms w])
              [m p] (mmul ctx m1 (subvec m2 1))]
          [(into [w] m)
           (k/trans (k/lemma "Int.mul_left_comm" (mon-expr ctx m1) atom (mon-expr ctx (subvec m2 1)))
                    (k/congr-mul (k/refl atom) p))])))))

(defn- padd
  "Proof of `P + Q = R` for normal forms. Returns `[R proof]`."
  [ctx P Q]
  (cond
    (empty? P) [Q (k/lemma "Int.zero_add" (poly-expr ctx Q))]
    (empty? Q) [P (k/lemma "Int.add_zero" (poly-expr ctx P))]
    :else
    (let [[c1 m1 :as t1] (first P), P' (subvec P 1)
          [c2 m2 :as t2] (first Q), Q' (subvec Q 1)
          te1 (term-expr ctx t1)
          te2 (term-expr ctx t2)
          order (compare m1 m2)]
      (cond
        (neg? order)
        (let [[R p] (padd ctx P' Q)]
          [(into [t1] R)
           (k/trans (k/lemma "Int.add_assoc" te1 (poly-expr ctx P') (poly-expr ctx Q))
                    (k/congr-add (k/refl te1) p))])

        (pos? order)
        (let [[R p] (padd ctx P Q')]
          [(into [t2] R)
           (k/trans (k/lemma "Int.add_left_comm" (poly-expr ctx P) te2 (poly-expr ctx Q'))
                    (k/congr-add (k/refl te2) p))])

        :else
        (let [m     (mon-expr ctx m1)
              c3    (+ c1 c2)
              [R p] (padd ctx P' Q')
              ;; (t1 + P') + (t2 + Q') = (t1 + t2) + (P' + Q')
              regroup (k/trans
                       (k/lemma "Int.add_assoc" te1 (poly-expr ctx P') (poly-expr ctx Q))
                       (k/congr-add (k/refl te1)
                                    (k/lemma "Int.add_left_comm" (poly-expr ctx P') te2 (poly-expr ctx Q')))
                       (k/symm (k/lemma "Int.add_assoc" te1 te2
                                        (k/add (poly-expr ctx P') (poly-expr ctx Q')))))
              ;; c1 * m + c2 * m = c3 * m
              combine (k/trans (k/symm (k/lemma "Int.add_mul" (k/lit c1) (k/lit c2) m))
                               (k/congr-mul (ground :add c1 c2) (k/refl m)))
              summed  (k/trans regroup (k/congr-add combine p))]
          (if (zero? c3)
            [R (k/trans summed
                        (k/congr-add (k/lemma "Int.zero_mul" m) (k/refl (poly-expr ctx R)))
                        (k/lemma "Int.zero_add" (poly-expr ctx R)))]
            [(into [[c3 m1]] R) summed]))))))

(defn- ttmul
  "Proof of `t₁ * t₂ = t₃ + 0` for terms. Returns `[[t₃] proof]`."
  [ctx [c1 m1] [c2 m2]]
  (let [M1 (mon-expr ctx m1)
        M2 (mon-expr ctx m2)
        [m p-mon] (mmul ctx m1 m2)
        c3 (* c1 c2)
        t3 (k/mul (k/lit c3) (mon-expr ctx m))]
    [[[c3 m]]
     (k/trans (k/lemma "Int.mul_assoc" (k/lit c1) M1 (k/mul (k/lit c2) M2))
              (k/congr-mul (k/refl (k/lit c1))
                           (k/lemma "Int.mul_left_comm" M1 (k/lit c2) M2))
              (k/symm (k/lemma "Int.mul_assoc" (k/lit c1) (k/lit c2) (k/mul M1 M2)))
              (with-rhs (k/congr-mul (ground :mul c1 c2) p-mon) t3)
              (k/symm (k/lemma "Int.add_zero" t3)))]))

(defn- tmul
  "Proof of `t * Q = R`. Returns `[R proof]`."
  [ctx t Q]
  (let [te (term-expr ctx t)]
    (if (empty? Q)
      [[] (k/lemma "Int.mul_zero" te)]
      (let [u (first Q), Q' (subvec Q 1)
            [T p1] (ttmul ctx t u)
            [R2 p2] (tmul ctx t Q')
            [R p3] (padd ctx T R2)]
        [R (k/trans (k/lemma "Int.mul_add" te (term-expr ctx u) (poly-expr ctx Q'))
                    (k/congr-add p1 p2)
                    p3)]))))

(defn- pmul
  "Proof of `P * Q = R`. Returns `[R proof]`."
  [ctx P Q]
  (if (empty? P)
    [[] (k/lemma "Int.zero_mul" (poly-expr ctx Q))]
    (let [t (first P), P' (subvec P 1)
          [R1 p1] (tmul ctx t Q)
          [R2 p2] (pmul ctx P' Q)
          [R p3] (padd ctx R1 R2)]
      [R (k/trans (k/lemma "Int.add_mul" (term-expr ctx t) (poly-expr ctx P') (poly-expr ctx Q))
                  (k/congr-add p1 p2)
                  p3)])))

(defn- normalize
  "Returns `[poly proof]` where `proof : e = poly-expr(poly)` and `e` is the
  canonical kernel spelling of `ir`."
  [ctx ir]
  (let [[op a b] ir]
    (case op
      :lit (if (zero? a)
             [[] (k/refl k/zero)]
             (let [c (k/lit a)]
               [[[a []]]
                (with-rhs (k/symm (k/trans (k/lemma "Int.add_zero" (k/mul c k/one))
                                           (k/lemma "Int.mul_one" c)))
                  (poly-expr ctx [[a []]]))]))
      :atom (let [x (get-in ctx [:atoms a])]
              [[[1N [a]]]
               (with-rhs (k/symm (k/trans (k/lemma "Int.add_zero" (k/mul k/one (k/mul x k/one)))
                                          (k/lemma "Int.one_mul" (k/mul x k/one))
                                          (k/lemma "Int.mul_one" x)))
                 (poly-expr ctx [[1N [a]]]))])
      :add (let [[A pa] (normalize ctx a)
                 [B pb] (normalize ctx b)
                 [R p] (padd ctx A B)]
             [R (k/trans (k/congr-add pa pb) p)])
      :mul (let [[A pa] (normalize ctx a)
                 [B pb] (normalize ctx b)
                 [R p] (pmul ctx A B)]
             [R (k/trans (k/congr-mul pa pb) p)])
      :neg (let [[A pa] (normalize ctx a)
                 [N pn] (normalize ctx [:lit -1N])
                 [R p] (pmul ctx N A)]
             [R (k/trans (k/lemma "Int.neg_eq_neg_one_mul" (:lhs pa))
                         (k/congr-mul pn pa)
                         p)])
      :sub (let [[R p] (normalize ctx [:add a [:neg b]])
                 [_ pa] (normalize ctx a)
                 [_ pb] (normalize ctx b)]
             [R (k/trans (k/lemma "Int.sub_eq_add_neg" (:lhs pa) (:lhs pb)) p)]))))

;; ## Rewriting
;;
;; Rules are equations with pattern variables. A global theorem's ∀-binders
;; become placeholder free variables; a hypothesis has none. Matching is
;; syntactic; the kernel re-checks every instantiated rule.

(def ^:private placeholder-ids (atom 8000000000))

(defn- const-rule [s]
  (let [ci (or (env/lookup (k/env) (name/from-string s))
               (throw (ex-info (str "int_ring: unknown rule " s) {:rule s})))
        _  (when (seq (env/ci-level-params ci))
             (throw (ex-info (str "int_ring: universe-polymorphic rules are not supported: " s)
                             {:rule s})))
        [ids body] (loop [t (env/ci-type ci) ids []]
                     (if (e/forall? t)
                       (let [id (swap! placeholder-ids inc)]
                         (recur (e/instantiate1 (e/forall-body t) (e/fvar id))
                                (conj ids id)))
                       [ids t]))]
    (if-let [view (k/eq-view body)]
      (assoc view :name s :ids ids)
      (if (env/def? ci)
        {:name s :unfold (name/from-string s)}
        (throw (ex-info (str "int_ring: rule " s " is neither an equation nor a definition")
                        {:rule s}))))))

(defn- hyp-rule [s fvar-id type]
  (let [view (or (k/eq-view type)
                 (throw (ex-info (str "int_ring: hypothesis " s " is not an equation")
                                 {:rule s})))]
    (assoc view :name s :ids [] :fvar (e/fvar fvar-id))))

(defn- resolve-rule [lctx sym]
  (let [s (str sym)]
    (if-let [[id decl] (first (filter (fn [[_ d]] (= s (:name d))) lctx))]
      (hyp-rule s id (:type decl))
      (const-rule s))))

(defn- match-pattern
  "Extends `subst` (placeholder id → expr) so that `pat` instantiates to
  `term`, or returns nil."
  [pat term ids subst]
  (cond
    (nil? subst) nil

    (and (e/fvar? pat) (contains? ids (e/fvar-id pat)))
    (let [id (e/fvar-id pat)]
      (if-let [bound (get subst id)]
        (when (= bound term) subst)
        (assoc subst id term)))

    (e/app? pat)
    (when (e/app? term)
      (->> subst
           (match-pattern (e/app-fn pat) (e/app-fn term) ids)
           (match-pattern (e/app-arg pat) (e/app-arg term) ids)))

    :else (when (= pat term) subst)))

(declare sort-level)

(defn- unfold-rule
  "Proof of `term = whnf(term)` if `term` applies the definition `rule`
  unfolds and reduces further, else nil."
  [st rule term]
  (let [head (e/get-app-fn term)]
    (when (and (e/const? head) (= (e/const-name head) (:unfold rule)))
      (let [term' (#'tc/cached-whnf st term)]
        (when (not= term' term)
          (let [type (tc/infer-type st term)
                level (sort-level st type)]
            (assoc (k/refl term' type level) :lhs term)))))))

(defn- apply-rule
  "Proof of `term = rhs` if `rule` applies to `term`, else nil."
  [st rule term]
  (if (:unfold rule)
    (unfold-rule st rule term)
    (let [ids (:ids rule)]
      (when-let [subst (match-pattern (:lhs rule) term (set ids) {})]
        (when (every? #(contains? subst %) ids)
          (let [vals (mapv subst ids)
                inst (fn [x] (e/instantiate (e/abstract-many x ids) vals))]
            {:lhs term
             :rhs (inst (:rhs rule))
             :type (inst (:type rule))
             :level (:level rule)
             :term (if-let [fv (:fvar rule)]
                     fv
                     (apply e/app* (k/const (:name rule)) vals))}))))))

(defn- sort-level [st type]
  (let [s (#'tc/cached-whnf st (tc/infer-type st type))]
    (when (e/sort? s) (e/sort-level s))))

(def ^:private max-rewrites 10000)

(defn- rewrite
  "Rewrites `term` bottom-up to a fixpoint with `rules`, returning a proof of
  `term = term'`."
  [st rules budget term]
  (when (neg? (swap! budget dec))
    (throw (ex-info "int_ring: rewriting did not terminate" {:term (k/->string term)})))
  (let [congruence
        (if-not (e/app? term)
          nil
          (let [[f args] (e/get-app-fn-args term)
                pas (mapv #(rewrite st rules budget %) args)]
            (when-not (every? k/refl? pas)
              (loop [i 0, g f, pf nil]
                (if (= i (count args))
                  pf
                  (let [arg (nth args i)
                        pi  (#'tc/cached-whnf st (tc/infer-type st g))
                        dom (e/forall-type pi)
                        cod (e/forall-body pi)
                        ;; Type arguments and instances sit behind dependent
                        ;; binders; they are left alone.
                        dependent? (e/has-loose-bvars? cod)
                        pa (when-not (or dependent? (k/refl? (nth pas i)))
                             (nth pas i))]
                    (when (and dependent? pf)
                      (throw (ex-info "int_ring: can't rewrite before a dependent argument"
                                      {:term (k/->string term)})))
                    (recur (inc i)
                           (e/app g arg)
                           (when (or pf pa)
                             (let [u (sort-level st dom)]
                               (k/congr-app g pf (or pa (k/refl arg dom u))
                                            {:dom dom :cod cod :u u
                                             :v (sort-level st cod)}))))))))))
        term' (if congruence (:rhs congruence) term)
        step  (some #(apply-rule st % term') rules)]
    (cond
      step (k/trans (or congruence (k/refl term (:type step) (:level step)))
                    step
                    (rewrite st rules budget (:rhs step)))
      congruence congruence
      :else (k/refl term))))

;; ## Public API

(defn prove-eq
  "Proves `lhs = rhs` (kernel `Int` terms, possibly containing free variables)
  as a polynomial identity over opaque atoms. Returns a proof map whose sides
  are the canonical spellings of `lhs` and `rhs` (definitionally equal to
  them), or throws `ex-info` with `:type ::not-an-identity` and the two normal
  forms if the sides differ as polynomials."
  [lhs rhs]
  (let [[ctx l-ir] (reify-term empty-ctx lhs)
        [ctx r-ir] (reify-term ctx rhs)
        [L pl] (normalize ctx l-ir)
        [R pr] (normalize ctx r-ir)]
    (when (not= L R)
      (throw (ex-info "int_ring: the sides are not equal as polynomials"
                      {:type ::not-an-identity
                       :lhs (k/->string (poly-expr ctx L))
                       :rhs (k/->string (poly-expr ctx R))})))
    (k/trans pl (k/symm pr))))

(defn linear-combination
  "Proves `lhs = rhs` in `Int` from hypotheses, like Lean's
  `linear_combination`. `hyps` is a sequence of `[coeff h]`, where `coeff` is a
  kernel `Int` term and `h` a proof map `{:lhs l :rhs r :term p}` with
  `p : l = r`. Succeeds when `lhs - rhs = Σ coeff·(l - r)` holds as a
  polynomial identity (checked by [[prove-eq]]); each `l - r` is then replaced
  by `0` using `Int.sub_eq_zero_of_eq`. Returns a proof map for `lhs = rhs`."
  [lhs rhs hyps]
  (let [diff (fn [{:keys [lhs rhs]}] (k/sub lhs rhs))
        spread (reduce (fn [acc [c h]] (k/add acc (k/mul c (diff h)))) rhs hyps)
        zeros  (reduce (fn [acc [c _]] (k/add acc (k/mul c k/zero))) rhs hyps)
        to-zero (reduce (fn [acc [c h]]
                          (k/congr-add acc
                                       (k/congr-mul (k/refl c)
                                                    (k/lemma "Int.sub_eq_zero_of_eq"
                                                             (:lhs h) (:rhs h) (:term h)))))
                        (k/refl rhs)
                        hyps)]
    (k/trans (prove-eq lhs spread)
             (assoc to-zero :lhs spread :rhs zeros)
             (prove-eq zeros rhs))))

(defn- goal-sides [goal-type]
  (let [[head args] (app-view goal-type)]
    (when-not (and (= head "Eq") (= 3 (count args)) (int-type? (args 0)))
      (throw (ex-info "int_ring: goal is not an equation in Int"
                      {:goal (k/->string goal-type)})))
    [(args 1) (args 2)]))

(defn int-ring
  "The `int_ring` tactic: closes the current goal, an `Int` equation that holds
  as a polynomial identity after rewriting with `rule-syms` (see the
  namespace docstring)."
  [ps rule-syms]
  (let [goal (or (proof/current-goal ps)
                 (throw (ex-info "int_ring: no goals" {})))
        [lhs rhs] (goal-sides (:type goal))
        rules (mapv #(resolve-rule (:lctx goal) %) rule-syms)
        st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))
        budget (atom max-rewrites)
        pl (if (seq rules) (rewrite st rules budget lhs) (k/refl lhs))
        pr (if (seq rules) (rewrite st rules budget rhs) (k/refl rhs))
        p (k/trans pl (prove-eq (:rhs pl) (:rhs pr)) (k/symm pr))]
    (-> ps
        (proof/assign-mvar (:id goal) {:kind :exact :term (:term p)})
        (proof/record-tactic :int_ring (vec rule-syms) (:id goal)))))

(defn- stuck-local
  "The id of a local variable of `lctx` that blocks unfolding an application
  of one of the `unfold` definitions in `expr`, or nil."
  [st lctx unfold expr]
  (letfn [(scrutinee [t]
            (let [head (e/get-app-fn t)]
              (when (and (e/const? head) (contains? unfold (e/const-name head)))
                (let [w (#'tc/cached-whnf st t)
                      [whead wargs] (e/get-app-fn-args w)]
                  (when (and (e/const? whead)
                             (re-find #"\.(rec|casesOn)$" (name/->string (e/const-name whead))))
                    (some (fn [arg]
                            (when (and (e/fvar? arg) (contains? lctx (e/fvar-id arg)))
                              (e/fvar-id arg)))
                          wargs))))))
          (walk [t]
            (or (scrutinee t)
                (when (e/app? t)
                  (or (walk (e/app-fn t)) (walk (e/app-arg t))))))]
    (walk expr)))

(defn int-ring-split
  "The `int_ring_split` tactic (see the namespace docstring)."
  [ps rule-syms]
  (let [goal (or (proof/current-goal ps)
                 (throw (ex-info "int_ring_split: no goals" {})))
        unfold (into #{} (keep :unfold) (map #(resolve-rule (:lctx goal) %) rule-syms))
        st (tc/attach-lctx (tc/mk-tc-state (:env ps)) (:lctx goal))]
    (if-let [fid (stuck-local st (:lctx goal) unfold (:type goal))]
      (let [before (count (:goals ps))
            ps (basic/cases ps fid)
            new-goals (- (count (:goals ps)) (dec before))]
        ;; `cases` replaces the current goal with its subgoals, in front.
        (reduce (fn [ps _] (int-ring-split ps rule-syms)) ps (range new-goals)))
      (int-ring ps rule-syms))))

(defn install!
  "Registers `int_ring` and `int_ring_split` with Ansatz's tactic registry.
  Idempotent."
  []
  (a/register-tactic! 'int_ring (fn [ps args] (int-ring ps (first args))))
  (a/register-tactic! 'int_ring_split (fn [ps args] (int-ring-split ps (first args)))))
