#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.order
  "Order reasoning on `Int` for the analysis library.

  - [[by-omega]] proves a linear-arithmetic goal from hypotheses. Every
    subterm that isn't linear integer arithmetic (a product of two variables,
    `num a`, `abs x`, …) is abstracted to a fresh variable, the resulting
    closed statement is proved by Ansatz's `omega`, and the proof is applied
    back to the original subterms. Nonlinear facts (e.g. `0 < a * b`) are
    passed in as hypotheses.
  - `Emmy.Analysis.Int.abs` with `abs_cases`, from which the other absolute
    value facts follow by case analysis and [[by-omega]].
  - Sign lemmas for products ([[mul-nonneg]]) and ring rewriting of
    propositions ([[rewrite-prop]]).

  [[install!]] adds the kernel theorems, all checked by `check-constant`
  without axioms beyond Init's."
  (:refer-clojure :exclude [abs])
  (:require [ansatz.core :as a]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]))

(def ^:private I k/int-type)
(def ^:private l0 level/zero)
(def ^:private l1 (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.Int.")
(defn- c [s] (k/const (str prefix s)))

(defn lt "`a < b` in `Int`." [a b] (t/app (k/const "LT.lt" l0) I (k/const "Int.instLTInt") a b))
(defn le "`a ≤ b` in `Int`." [a b] (t/app (k/const "LE.le" l0) I (k/const "Int.instLEInt") a b))

;; ## by-omega

(defn- head+args [x]
  (let [[h args] (e/get-app-fn-args x)]
    [(when (e/const? h) (name/->string (e/const-name h))) (vec args)]))

(defn- numeral? [x]
  (let [[h args] (head+args x)]
    (or (e/lit-nat? x)
        (and (= h "OfNat.ofNat") (= 3 (count args)))
        (and (= h "Int.ofNat") (= 1 (count args)) (e/lit-nat? (args 0)))
        (and (#{"Neg.neg" "Int.neg"} h) (numeral? (peek args))))))

(defn- binop [h a b]
  (case h
    ("HAdd.hAdd" "Int.add") (k/add a b)
    ("HSub.hSub" "Int.sub") (k/sub a b)))

(defn- abstract-term
  "Replaces the non-linear subterms of the `Int` term `x` by fresh fvars,
  recorded in the `atoms` atom (expr → fvar, with insertion order)."
  [atoms x]
  (let [[h args] (head+args x)
        n (count args)
        recur* #(abstract-term atoms %)
        atom! (fn []
                (or (get-in @atoms [:map x])
                    (let [fv (e/fvar (swap! (:ids @atoms) inc))]
                      (swap! atoms #(-> % (assoc-in [:map x] fv) (update :order conj x)))
                      fv)))]
    (cond
      (numeral? x)
      x

      ;; Typeclass operations carry type and instance arguments before operands.
      (and (#{"HAdd.hAdd" "HSub.hSub"} h) (= n 6))
      (binop h (recur* (args 4)) (recur* (args 5)))

      (and (#{"Int.add" "Int.sub"} h) (= n 2))
      (binop h (recur* (args 0)) (recur* (args 1)))

      (and (#{"Neg.neg"} h) (= n 3))
      (k/neg (recur* (args 2)))

      (and (#{"Int.neg"} h) (= n 1))
      (k/neg (recur* (args 0)))

      ;; Multiplication stays linear only when one operand is a numeral.
      (and (= h "HMul.hMul") (= n 6) (numeral? (args 4)))
      (k/mul (args 4) (recur* (args 5)))

      (and (= h "HMul.hMul") (= n 6) (numeral? (args 5)))
      (k/mul (recur* (args 4)) (args 5))

      :else (atom!))))

(defn- abstract-prop [atoms p]
  (let [[h args] (head+args p)
        n (count args)]
    (cond
      (and (#{"LT.lt" "LE.le"} h) (= n 4))
      (t/app (e/get-app-fn p) (args 0) (args 1)
             (abstract-term atoms (args 2)) (abstract-term atoms (args 3)))
      (and (= h "Eq") (= n 3) (= (args 0) I))
      (k/eq (abstract-term atoms (args 1)) (abstract-term atoms (args 2)))
      (and (= h "Not") (= n 1)) (t/not' (abstract-prop atoms (args 0)))
      (and (#{"And" "Or"} h) (= n 2))
      (t/app (e/get-app-fn p) (abstract-prop atoms (args 0)) (abstract-prop atoms (args 1)))
      (= h "False") p
      :else (throw (ex-info "by-omega: unsupported proposition" {:prop (k/->string p)})))))

(defonce ^:private omega-ids (atom 9000000000))

(defn- omega-raw
  "`by-omega` without normalization: abstracts atoms syntactically."
  [goal hyps]
  (let [atoms (atom {:map {} :order [] :ids omega-ids})
        goal' (abstract-prop atoms goal)
        hyps' (mapv (fn [[p _]] (abstract-prop atoms p)) hyps)
        order (:order @atoms)
        fvars (mapv #(get-in @atoms [:map %]) order)
        hyp-ids (vec (repeatedly (count hyps) #(swap! omega-ids inc)))
        body (reduce (fn [acc [hp id]] (e/forall' (str "h" id) hp (e/abstract1 acc id) :default))
                     goal'
                     (reverse (map vector hyps' hyp-ids)))
        closed (reduce (fn [acc fv] (e/forall' (str "z" (e/fvar-id fv)) I
                                               (e/abstract1 acc (e/fvar-id fv)) :default))
                       body
                       (reverse fvars))
        names (mapv #(str "v" %) (range (+ (count fvars) (count hyps))))
        [_ proof] (k/quietly (a/prove-law names closed '[(omega)]))]
    (apply t/app proof (concat order (map second hyps)))))

(defn- relation-sides
  "`[rebuild lhs rhs]` for an `Int` `<`, `≤` or `=`, else nil. `rebuild` makes
  the same relation between new sides."
  [p]
  (let [[h args] (head+args p)
        n (count args)]
    (cond
      (and (#{"LT.lt" "LE.le"} h) (= n 4) (= (args 0) I))
      [(fn [x y] (t/app (e/get-app-fn p) (args 0) (args 1) x y)) (args 2) (args 3)]
      (and (= h "Eq") (= n 3) (= (args 0) I))
      [k/eq (args 1) (args 2)])))

(def ^:private max-omega-coefficient 64)

(defn- literal-value
  "Integer value of a numeral term, or nil."
  [x]
  (let [[h args] (head+args x)]
    (cond
      (and (= h "OfNat.ofNat") (= 3 (count args)) (e/lit-nat? (args 1)))
      (bigint (e/lit-nat-val (args 1)))
      (and (= h "Neg.neg") (= 3 (count args))) (some-> (literal-value (args 2)) -)
      :else nil)))

(defn- monomial-base
  "`m` for a normal-form monomial `v₁ * (v₂ * … * 1)`: the single atom for
  degree one (dropping `* 1`), the product itself otherwise."
  [m]
  (let [[h args] (head+args m)]
    (if (and (= h "HMul.hMul") (= 6 (count args)) (= 1 (literal-value (args 5))))
      (args 4)
      m)))

(defn- omega-spelling
  "Respells a ring normal form `c₁·m₁ + (c₂·m₂ + … + 0)` for Ansatz's `omega`,
  which handles addition, negation and numerals but no multiplication by
  literals: `c·m` becomes `m + … + m` (|c| times, negated if `c < 0`)."
  [x]
  (let [[h args] (head+args x)]
    (if (and (= h "HAdd.hAdd") (= 6 (count args)))
      (let [[_ [_ _ _ _ coeff mon]] (head+args (args 4))
            c (literal-value coeff)
            rest' (omega-spelling (args 5))]
        (when (> (clojure.core/abs c) max-omega-coefficient)
          (throw (ex-info "by-omega: coefficient too large" {:coefficient c})))
        (if (= 1 (literal-value mon))
          (k/add (k/lit c) rest')
          (let [base (monomial-base mon)
                sum (reduce k/add (repeat (clojure.core/abs c) base))]
            (k/add (if (neg? c) (k/neg sum) sum) rest'))))
      x)))

(defn- omega-normal-forms
  "Like `alg/normalize-terms`, respelled for `omega`: `[[nf proof] …]`."
  [terms]
  (mapv (fn [[nf p]]
          (let [nf' (omega-spelling nf)]
            (if (= nf nf')
              [nf p]
              [nf' (k/trans p (assoc (alg/prove-eq nf nf') :lhs nf :rhs nf'))])))
        (alg/normalize-terms terms)))

(defn by-omega
  "Proof term of the proposition `goal` from `hyps`, a sequence of
  `[prop proof]`. The sides of every `<`, `≤` and `=` are first ring-normalized
  with one shared atom order (so `(a+1)·d` and `a·d + d` agree), then
  non-linear monomials are abstracted to variables and the statement is proved
  by `omega`. Supported propositions are `<`, `≤`, `=` on `Int`, `¬`, `∧`, `∨`
  and `False`. Throws if `omega` fails."
  [goal hyps]
  (let [props (cons goal (map first hyps))
        rels (map relation-sides props)
        sides (vec (mapcat (fn [r] (when r [(nth r 1) (nth r 2)])) rels))
        normal (omega-normal-forms sides)
        ;; per proposition: [normalized prop, proof prop = normalized prop]
        normalize (fn [p r offset]
                    (if-not r
                      [p nil]
                      (let [[rebuild x y] r
                            [nx px] (normal offset)
                            [ny py] (normal (inc offset))]
                        [(rebuild nx ny) [rebuild x y nx ny px py]])))
        [norm-props _] (reduce (fn [[acc offset] [p r]]
                                 [(conj acc (normalize p r offset)) (if r (+ offset 2) offset)])
                               [[] 0]
                               (map vector props rels))
        ;; transport h : R(x, y) to R(nx, ny), one side at a time
        forward (fn [h [rebuild _ y nx _ px py]]
                  (let [h1 (t/transport (t/lam "z" I #(rebuild % y)) px h)]
                    (t/transport (t/lam "z" I #(rebuild nx %)) py h1)))
        backward (fn [h [rebuild x _ _ ny px py]]
                   (let [h1 (t/transport (t/lam "z" I #(rebuild % ny)) (k/symm px) h)]
                     (t/transport (t/lam "z" I #(rebuild x %)) (k/symm py) h1)))
        [[goal' goal-info] & hyp-norms] norm-props
        hyps' (mapv (fn [[_ proof] [np info]] [np (if info (forward proof info) proof)])
                    hyps hyp-norms)
        proof (omega-raw goal' hyps')]
    (if goal-info (backward proof goal-info) proof)))

;; ## Rewriting propositions

(defn rewrite-prop
  "Proof of `(motive y)` from `h : motive x`, where `x = y` holds as a ring
  identity in `Int` (proved by `int_ring`). `motive` is a Clojure function from
  an `Int` term to a proposition."
  [motive x y h]
  (let [p (alg/prove-eq x y)]
    (t/transport (t/lam "z" I motive) (assoc p :lhs x :rhs y) h)))

;; ## Kernel theorems

(def ^:private decl (t/declarer prefix))
(def ^:private theorem (t/with-kind decl :thm))
(def ^:private define (t/with-kind decl :def))

(defn abs "Kernel term `Emmy.Analysis.Int.abs a`." [x] (t/app (c "abs") x))

(defn mul-nonneg
  "Proof of `0 ≤ a * b` from `ha : 0 ≤ a` and `hb : 0 ≤ b`."
  [a b ha hb]
  (t/app (c "mul_nonneg") a b ha hb))

(defn abs-cases
  "Proof of `(0 ≤ a ∧ abs a = a) ∨ (a < 0 ∧ abs a = -a)`."
  [a]
  (t/app (c "abs_cases") a))

(defn with-abs-cases
  "Proof of `goal` by case analysis on the sign of each term in `xs`. `f`
  receives the accumulated facts (`[prop proof]` pairs: the sign of `x` and
  `abs x = ±x`) and returns a proof of `goal` for that case."
  [xs goal f]
  (letfn [(go [xs facts]
            (if (empty? xs)
              (f facts)
              (let [x (first xs)
                    pos (t/and' (le k/zero x) (k/eq (abs x) x))
                    neg (t/and' (lt x k/zero) (k/eq (abs x) (k/neg x)))
                    branch (fn [p sign value]
                             (t/lam "h" p
                                    (fn [h]
                                      (go (rest xs)
                                          (conj facts
                                                [sign (t/and-left sign value h)]
                                                [value (t/and-right sign value h)])))))]
                (t/or-elim pos neg goal (abs-cases x)
                           (branch pos (le k/zero x) (k/eq (abs x) x))
                           (branch neg (lt x k/zero) (k/eq (abs x) (k/neg x)))))))]
    (go (vec xs) [])))

(defn install
  "Pure. Declares the `Int` order and absolute-value theorems into `ctx`."
  [ctx]
  (as-> ctx ctx
    (theorem ctx "lt_trans"
      (t/forall [[x I] [y I] [z I]] (t/arrow (lt x y) (t/arrow (lt y z) (lt x z))))
      (t/lambda [[x I] [y I] [z I] [h1 (lt x y)] [h2 (lt y z)]]
        (by-omega (lt x z) [[(lt x y) h1] [(lt y z) h2]])))
    (theorem ctx "add_pos"
      (t/forall [[x I] [y I]] (t/arrow (lt k/zero x) (t/arrow (lt k/zero y) (lt k/zero (k/add x y)))))
      (t/lambda [[x I] [y I] [hx (lt k/zero x)] [hy (lt k/zero y)]]
        (by-omega (lt k/zero (k/add x y)) [[(lt k/zero x) hx] [(lt k/zero y) hy]])))
    (theorem ctx "add_nonneg"
      (t/forall [[x I] [y I]] (t/arrow (le k/zero x) (t/arrow (le k/zero y) (le k/zero (k/add x y)))))
      (t/lambda [[x I] [y I] [hx (le k/zero x)] [hy (le k/zero y)]]
        (by-omega (le k/zero (k/add x y)) [[(le k/zero x) hx] [(le k/zero y) hy]])))
    (theorem ctx "mul_nonneg"
      (t/forall [[x I] [y I]] (t/arrow (le k/zero x) (t/arrow (le k/zero y) (le k/zero (k/mul x y)))))
      (t/lambda [[x I] [y I] [hx (le k/zero x)] [hy (le k/zero y)]]
        ;; x·0 ≤ x·y, then rewrite x·0 to 0
        (rewrite-prop #(le % (k/mul x y)) (k/mul x k/zero) k/zero
                      (t/app (k/const "Int.mul_le_mul_of_nonneg_left") k/zero y x hy hx))))

    (theorem ctx "lt_of_mul_lt_mul_right"
      (t/forall [[x I] [y I] [z I]]
        (t/arrow (lt k/zero z) (t/arrow (lt (k/mul x z) (k/mul y z)) (lt x y))))
      (t/lambda [[x I] [y I] [z I] [hz (lt k/zero z)] [h (lt (k/mul x z) (k/mul y z))]]
        (let [goal (lt x y)]
          (t/or-elim goal (t/not' goal) goal
                     (t/decidable-em goal (t/app (k/const "Int.decLt") x y))
                     (t/lam "yes" goal identity)
                     (t/lam "no" (t/not' goal)
                            (fn [no]
                              (let [hle (t/app (k/const "Iff.mp") (t/not' goal) (le y x)
                                               (t/app (k/const "Int.not_lt") x y) no)
                                    ;; z·y ≤ z·x, contradicting x·z < y·z
                                    mono (t/app (k/const "Int.mul_le_mul_of_nonneg_left") y x z hle
                                                (t/app (k/const "Int.le_of_lt") k/zero z hz))]
                                (t/false-elim goal
                                              (by-omega t/false-prop
                                                        [[(lt (k/mul x z) (k/mul y z)) h]
                                                         [(le (k/mul z y) (k/mul z x)) mono]])))))))))
    (theorem ctx "mul_self_pos"
      (t/forall [[x I]] (t/arrow (t/not' (k/eq x k/zero)) (lt k/zero (k/mul x x))))
      (t/lambda [[x I] [hne (t/not' (k/eq x k/zero))]]
        (let [goal (lt k/zero (k/mul x x))
              neg (lt x k/zero) zero (k/eq x k/zero) pos (lt k/zero x)
              rest (t/or' zero pos)]
          (t/or-elim neg rest goal (t/app (k/const "Int.lt_trichotomy") x k/zero)
                     (t/lam "h" neg
                            (fn [h]
                              (let [nx (k/neg x)
                                    hn (by-omega (lt k/zero nx) [[neg h]])]
                                (by-omega goal [[(lt k/zero (k/mul nx nx))
                                                 (t/app (k/const "Int.mul_pos") nx nx hn hn)]]))))
                     (t/lam "h" rest
                            (fn [h]
                              (t/or-elim zero pos goal h
                                         (t/lam "h0" zero (fn [h0] (t/absurd' zero goal h0 hne)))
                                         (t/lam "hp" pos
                                                (fn [hp] (t/app (k/const "Int.mul_pos") x x hp hp))))))))))

    (theorem ctx "le_of_mul_le_mul_right"
      (t/forall [[x I] [y I] [z I]]
        (t/arrow (lt k/zero z) (t/arrow (le (k/mul x z) (k/mul y z)) (le x y))))
      (t/lambda [[x I] [y I] [z I] [hz (lt k/zero z)] [h (le (k/mul x z) (k/mul y z))]]
        (let [goal (le x y)]
          (t/or-elim goal (t/not' goal) goal
                     (t/decidable-em goal (t/app (k/const "Int.decLe") x y))
                     (t/lam "yes" goal identity)
                     (t/lam "no" (t/not' goal)
                            (fn [no]
                              (let [hlt (t/app (k/const "Iff.mp") (t/not' goal) (lt y x)
                                               (t/app (k/const "Int.not_le") x y) no)
                                    ;; z·y < z·x, contradicting x·z ≤ y·z
                                    mono (t/app (k/const "Int.mul_lt_mul_of_pos_left") y x z hlt hz)]
                                (t/false-elim goal
                                              (by-omega t/false-prop
                                                        [[(le (k/mul x z) (k/mul y z)) h]
                                                         [(lt (k/mul z y) (k/mul z x)) mono]])))))))))

    (define ctx "abs" (t/arrow I I)
      (t/lambda [[x I]]
        (t/app (k/const "ite" l1) I (le k/zero x) (t/app (k/const "Int.decLe") k/zero x)
               x (k/neg x))))
    (theorem ctx "abs_cases"
      (t/forall [[x I]]
        (t/or' (t/and' (le k/zero x) (k/eq (abs x) x))
               (t/and' (lt x k/zero) (k/eq (abs x) (k/neg x)))))
      (t/lambda [[x I]]
        (let [nonneg (le k/zero x)
              inst (t/app (k/const "Int.decLe") k/zero x)
              pos (t/and' nonneg (k/eq (abs x) x))
              neg (t/and' (lt x k/zero) (k/eq (abs x) (k/neg x)))
              goal (t/or' pos neg)]
          (t/or-elim nonneg (t/not' nonneg) goal (t/decidable-em nonneg inst)
                     (t/lam "h" nonneg
                            (fn [h]
                              (t/or-inl pos neg
                                        (t/and-intro nonneg (k/eq (abs x) x) h
                                                     (t/app (k/const "if_pos" l1) nonneg inst h I
                                                            x (k/neg x))))))
                     (t/lam "h" (t/not' nonneg)
                            (fn [h]
                              (t/or-inr pos neg
                                        (t/and-intro (lt x k/zero) (k/eq (abs x) (k/neg x))
                                                     (t/app (k/const "Iff.mp") (t/not' nonneg) (lt x k/zero)
                                                            (t/app (k/const "Int.not_le") k/zero x) h)
                                                     (t/app (k/const "if_neg" l1) nonneg inst h I
                                                            x (k/neg x))))))))))
    (reduce (fn [ctx [label vars goal-fn abs-terms]]
              (theorem ctx label
                (if (= 1 (count vars))
                  (t/forall [[x I]] (goal-fn x))
                  (t/forall [[x I] [y I]] (goal-fn x y)))
                (if (= 1 (count vars))
                  (t/lambda [[x I]]
                    (with-abs-cases (abs-terms x) (goal-fn x) #(by-omega (goal-fn x) %)))
                  (t/lambda [[x I] [y I]]
                    (with-abs-cases (abs-terms x y) (goal-fn x y) #(by-omega (goal-fn x y) %))))))
            ctx
            [["abs_nonneg" '[x] (fn [x] (le k/zero (abs x))) (fn [x] [x])]
             ["le_abs" '[x] (fn [x] (le x (abs x))) (fn [x] [x])]
             ["neg_le_abs" '[x] (fn [x] (le (k/neg x) (abs x))) (fn [x] [x])]
             ["abs_neg" '[x] (fn [x] (k/eq (abs (k/neg x)) (abs x))) (fn [x] [x (k/neg x)])]
             ["abs_triangle" '[x y]
              (fn [x y] (le (abs (k/add x y)) (k/add (abs x) (abs y))))
              (fn [x y] [x y (k/add x y)])]
             ["abs_sub_comm" '[x y]
              (fn [x y] (k/eq (abs (k/sub x y)) (abs (k/sub y x))))
              (fn [x y] [(k/sub x y) (k/sub y x)])]])
    (theorem ctx "abs_of_pos"
      (t/forall [[x I]] (t/arrow (lt k/zero x) (k/eq (abs x) x)))
      (t/lambda [[x I] [h (lt k/zero x)]]
        (with-abs-cases [x] (k/eq (abs x) x)
          #(by-omega (k/eq (abs x) x) (conj % [(lt k/zero x) h])))))
    (theorem ctx "abs_lt"
      (t/forall [[x I] [b I]]
        (t/iff (lt (abs x) b) (t/and' (lt (k/neg b) x) (lt x b))))
      (t/lambda [[x I] [b I]]
        (let [lhs (lt (abs x) b) rhs (t/and' (lt (k/neg b) x) (lt x b))]
          (t/iff-intro lhs rhs
                       (t/lam "h" lhs
                              (fn [h]
                                (with-abs-cases [x] rhs
                                  (fn [facts]
                                    (t/and-intro (lt (k/neg b) x) (lt x b)
                                                 (by-omega (lt (k/neg b) x) (conj facts [lhs h]))
                                                 (by-omega (lt x b) (conj facts [lhs h])))))))
                       (t/lam "h" rhs
                              (fn [h]
                                (with-abs-cases [x] lhs
                                  (fn [facts]
                                    (by-omega lhs (conj facts
                                                        [(lt (k/neg b) x) (t/and-left (lt (k/neg b) x) (lt x b) h)]
                                                        [(lt x b) (t/and-right (lt (k/neg b) x) (lt x b) h)]))))))))))
    (theorem ctx "abs_mul"
      (t/forall [[x I] [y I]] (k/eq (abs (k/mul x y)) (k/mul (abs x) (abs y))))
      (t/lambda [[x I] [y I]]
        (let [goal (k/eq (abs (k/mul x y)) (k/mul (abs x) (abs y)))]
          (with-abs-cases [x y (k/mul x y)] goal
            (fn [facts]
              ;; facts: sign x, abs x = ±x, sign y, abs y = ±y, sign xy, abs xy = ±xy
              (let [[[sx hsx] [ex hex] [sy hsy] [ey hey] [sxy hsxy] [exy hexy]] facts
                    rhs-x (last (e/get-app-args ex))
                    rhs-y (last (e/get-app-args ey))
                    ;; abs x · abs y = (±x)(±y), by congruence on the case equations
                    p1 (k/congr-mul {:lhs (abs x) :rhs rhs-x :term hex}
                                    {:lhs (abs y) :rhs rhs-y :term hey})
                    sign (if (= rhs-x x) (if (= rhs-y y) 1 -1) (if (= rhs-y y) -1 1))
                    target (if (= 1 sign) (k/mul x y) (k/neg (k/mul x y)))
                    p2 (alg/prove-eq (:rhs p1) target)
                    rhs= (k/trans p1 p2)                 ; abs x · abs y = ±(x·y)
                    ;; the sign of x·y is forced by the signs of x and y
                    xy-sign (let [nx (if (= rhs-x x) x (k/neg x))
                                  ny (if (= rhs-y y) y (k/neg y))
                                  nn (mul-nonneg nx ny
                                                 (by-omega (le k/zero nx) [[sx hsx]])
                                                 (by-omega (le k/zero ny) [[sy hsy]]))]
                              [(le k/zero (k/mul nx ny)) nn])
                    lhs= (by-omega (k/eq (abs (k/mul x y)) target)
                                   [[sxy hsxy] [exy hexy]
                                    (let [[p pf] xy-sign]
                                      ;; restate 0 ≤ (±x)(±y) as 0 ≤ ±(x·y)
                                      [(le k/zero target)
                                       (rewrite-prop #(le k/zero %) (last (e/get-app-args p)) target pf)])])]
                (:term (k/trans {:lhs (abs (k/mul x y)) :rhs target :term lhs=}
                                (k/symm rhs=)))))))))))

(defn install!
  "Installs the `Int` order and absolute-value theorems. Idempotent."
  []
  (k/ensure-init!)
  (alg/install!)
  (locking k/install-lock
    (k/commit! install))
  :installed)
