#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.simplify
  "Verified simplification of polynomial expressions.

  Inside Ansatz (installed by [[install!]]):

  ```
  Emmy.PolyExpr.mkAdd, mkMul : PolyExpr → PolyExpr → PolyExpr   -- smart constructors
  Emmy.PolyExpr.mkNeg        : PolyExpr → PolyExpr
  Emmy.PolyExpr.simp         : PolyExpr → PolyExpr             -- bottom-up rebuild

  theorem Emmy.PolyExpr.simp_correct (e : PolyExpr) (x : Int) (ρ : Nat → Int) :
    Emmy.Analysis.Rational.Equiv (value x ρ (simp e)) (value x ρ e)
  ```

  The smart constructors drop additive zeros and multiplicative ones,
  annihilate with zero, fold integer constant arithmetic, negate constants and
  fractions, and cancel double negation. Fractions are not folded with each
  other; Emmy's simplifier does that downstream.
  Each has its own correctness lemma, e.g. `mkAdd_correct`, stating
  `value (mkAdd p q)` and `value (add p q)` are equivalent rationals (as the
  cross-multiplied `Int` equation). They are proved by `int_ring_split`, which
  case-splits on the constructors and integer literals the definition
  inspects. `simp_correct` then follows by induction, chaining each
  constructor lemma by `Rational.equiv_trans` with `Rational.add_congr`,
  `mul_congr` or `neg_congr` on the induction hypotheses.

  `simp` is deliberately local. It doesn't collect like terms or reorder
  (`x + x` stays as it is); that is Emmy's canonical simplifier's job
  downstream.

  The smart constructors are written with nested patterns such as
  `(Emmy.PolyExpr.const (Int.ofNat 0))`; [[emmy.ansatz.match]] compiles them
  into shapes Ansatz can elaborate, and the `Int.rec` lowering registered by
  [[emmy.ansatz.core/ensure-init!]] runs them natively."
  (:require [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.rational :as rat]
            [emmy.ansatz.codegen :as codegen]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]))

(def simp-name "Emmy.PolyExpr.simp")
(def theorem-name "Emmy.PolyExpr.simp_correct")

;; ## Smart constructors

(def ^:private smart-constructors
  '[[Emmy.PolyExpr.mkAdd [p :- Emmy.PolyExpr q :- Emmy.PolyExpr]
     (match p
       [(Emmy.PolyExpr.const (Int.ofNat 0)) q]
       [(Emmy.PolyExpr.const c)
        (match q
          [(Emmy.PolyExpr.const (Int.ofNat 0)) p]
          [(Emmy.PolyExpr.const d) (Emmy.PolyExpr.const (Int.add c d))]
          [_ (Emmy.PolyExpr.add p q)])]
       [_ (match q
            [(Emmy.PolyExpr.const (Int.ofNat 0)) p]
            [_ (Emmy.PolyExpr.add p q)])])]
    [Emmy.PolyExpr.mkMul [p :- Emmy.PolyExpr q :- Emmy.PolyExpr]
     (match p
       [(Emmy.PolyExpr.const (Int.ofNat 0)) (Emmy.PolyExpr.const 0)]
       [(Emmy.PolyExpr.const (Int.ofNat 1)) q]
       [(Emmy.PolyExpr.const c)
        (match q
          [(Emmy.PolyExpr.const (Int.ofNat 0)) (Emmy.PolyExpr.const 0)]
          [(Emmy.PolyExpr.const (Int.ofNat 1)) p]
          [(Emmy.PolyExpr.const d) (Emmy.PolyExpr.const (Int.mul c d))]
          [_ (Emmy.PolyExpr.mul p q)])]
       [_ (match q
            [(Emmy.PolyExpr.const (Int.ofNat 0)) (Emmy.PolyExpr.const 0)]
            [(Emmy.PolyExpr.const (Int.ofNat 1)) p]
            [_ (Emmy.PolyExpr.mul p q)])])]
    [Emmy.PolyExpr.mkNeg [p :- Emmy.PolyExpr]
     (match p
       [(Emmy.PolyExpr.const c) (Emmy.PolyExpr.const (Int.neg c))]
       [(Emmy.PolyExpr.frac n k) (Emmy.PolyExpr.frac (Int.neg n) k)]
       [(Emmy.PolyExpr.neg a) a]
       [_ (Emmy.PolyExpr.neg p)])]])

(def ^:private semantic-rules
  (mapv first ax/semantic-equations))

(defn- cross
  "`num x ρ l · den r = num x ρ r · den l`: `value x ρ l` and `value x ρ r`
  are `Rational.Equiv`, stated as an `Int` equation for `int_ring_split`."
  [l r]
  (list '= 'Int
        (list 'Int.mul (list 'Emmy.PolyExpr.num 'x 'rho l) (list 'Emmy.PolyExpr.den r))
        (list 'Int.mul (list 'Emmy.PolyExpr.num 'x 'rho r) (list 'Emmy.PolyExpr.den l))))

(def ^:private smart-constructor-lemmas
  ;; [name params statement definition-to-unfold]; each statement is
  ;; definitionally `Equiv (value x ρ (mk… p q)) (value x ρ (… p q))`.
  [['Emmy.PolyExpr.mkAdd_correct '[p :- Emmy.PolyExpr q :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
    (cross '(Emmy.PolyExpr.mkAdd p q) '(Emmy.PolyExpr.add p q))
    '[Emmy.PolyExpr.mkAdd]]
   ['Emmy.PolyExpr.mkMul_correct '[p :- Emmy.PolyExpr q :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
    (cross '(Emmy.PolyExpr.mkMul p q) '(Emmy.PolyExpr.mul p q))
    '[Emmy.PolyExpr.mkMul]]
   ['Emmy.PolyExpr.mkNeg_correct '[p :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
    (cross '(Emmy.PolyExpr.mkNeg p) '(Emmy.PolyExpr.neg p))
    '[Emmy.PolyExpr.mkNeg]]])

;; ## simp

(def ^:private simp-body
  '(match e
     [(Emmy.PolyExpr.const c) (Emmy.PolyExpr.const c)]
     [(Emmy.PolyExpr.X) Emmy.PolyExpr.X]
     [(Emmy.PolyExpr.add a b)
      (Emmy.PolyExpr.mkAdd (Emmy.PolyExpr.simp a) (Emmy.PolyExpr.simp b))]
     [(Emmy.PolyExpr.mul a b)
      (Emmy.PolyExpr.mkMul (Emmy.PolyExpr.simp a) (Emmy.PolyExpr.simp b))]
     [(Emmy.PolyExpr.neg a) (Emmy.PolyExpr.mkNeg (Emmy.PolyExpr.simp a))]
     [(Emmy.PolyExpr.param j) (Emmy.PolyExpr.param j)]
     [(Emmy.PolyExpr.frac p q) (Emmy.PolyExpr.frac p q)]))

(def ^:private simp-equations
  '[[Emmy.PolyExpr.simp_const [c :- Int]
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp (Emmy.PolyExpr.const c)) (Emmy.PolyExpr.const c))]
    [Emmy.PolyExpr.simp_X []
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp Emmy.PolyExpr.X) Emmy.PolyExpr.X)]
    [Emmy.PolyExpr.simp_add [a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp (Emmy.PolyExpr.add a b))
        (Emmy.PolyExpr.mkAdd (Emmy.PolyExpr.simp a) (Emmy.PolyExpr.simp b)))]
    [Emmy.PolyExpr.simp_mul [a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp (Emmy.PolyExpr.mul a b))
        (Emmy.PolyExpr.mkMul (Emmy.PolyExpr.simp a) (Emmy.PolyExpr.simp b)))]
    [Emmy.PolyExpr.simp_neg [a :- Emmy.PolyExpr]
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp (Emmy.PolyExpr.neg a))
        (Emmy.PolyExpr.mkNeg (Emmy.PolyExpr.simp a)))]
    [Emmy.PolyExpr.simp_param [j :- Nat]
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp (Emmy.PolyExpr.param j)) (Emmy.PolyExpr.param j))]
    [Emmy.PolyExpr.simp_frac [p :- Int q :- Nat]
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp (Emmy.PolyExpr.frac p q)) (Emmy.PolyExpr.frac p q))]])

(defn- value-of [e] (list 'Emmy.PolyExpr.value 'x 'rho e))

(def ^:private simp-sym 'Emmy.PolyExpr.simp)

(defn- chain
  "`exact` step for a node rebuilt by smart constructor `mk` from simplified
  children: `Equiv (value (mk sa…)) (value (op sa…))` from `mk-lemma`, then
  `Equiv (value (op sa…)) (value (op a…))` from `congr` on the hypotheses."
  [mk op mk-lemma congr children ihs]
  (let [simplified (map #(list simp-sym %) children)
        congr-args (mapcat (fn [s c] [(value-of s) (value-of c)]) simplified children)]
    (list 'exact
          (list 'Emmy.Analysis.Rational.equiv_trans
                (value-of (apply list mk simplified))
                (value-of (apply list op simplified))
                (value-of (apply list op children))
                (concat (list mk-lemma) simplified '(x rho))
                (concat (list congr) congr-args ihs)))))

(defn- leaf [ctor-app]
  (list 'exact (list 'Emmy.Analysis.Rational.equiv_refl (value-of ctor-app))))

(def ^:private theorem-proof
  ;; Cases in constructor order: const, X, add, mul, neg, param, frac.
  ['(induction e)
   (leaf '(Emmy.PolyExpr.const c))
   (leaf 'Emmy.PolyExpr.X)
   (chain 'Emmy.PolyExpr.mkAdd 'Emmy.PolyExpr.add 'Emmy.PolyExpr.mkAdd_correct
          'Emmy.Analysis.Rational.add_congr '[a b] '[ih_a ih_b])
   (chain 'Emmy.PolyExpr.mkMul 'Emmy.PolyExpr.mul 'Emmy.PolyExpr.mkMul_correct
          'Emmy.Analysis.Rational.mul_congr '[a b] '[ih_a ih_b])
   (chain 'Emmy.PolyExpr.mkNeg 'Emmy.PolyExpr.neg 'Emmy.PolyExpr.mkNeg_correct
          'Emmy.Analysis.Rational.neg_congr '[a] '[ih_a])
   (leaf '(Emmy.PolyExpr.param j))
   (leaf '(Emmy.PolyExpr.frac fnum fden))])

(defn- install-smart-constructor-lemmas [ctx]
  (reduce (fn [ctx [nm params prop unfold]]
            (t/declare-theorem ctx (str nm) params prop
              [(list 'int_ring_split (into unfold semantic-rules))]))
          ctx smart-constructor-lemmas))

(defn- install-theorem [ctx]
  (t/declare-theorem ctx theorem-name '[e x rho]
    (t/forall [[e ax/poly-type] [x k/int-type] [rho ax/env-type]]
      (rat/equiv (ax/value-term x rho (t/app (k/const simp-name) e))
                 (ax/value-term x rho e)))
    theorem-proof))

(defn install-theorems
  "Pure. Proves and declares the smart constructors' correctness lemmas,
  `simp`'s equation lemmas and `simp_correct` into `ctx`. Assumes the smart
  constructors and `simp` -- compiled functions, not ctx-threadable, see
  [[install!]] -- are already present in `ctx`'s environment.

  Deliberately not named `install`: `emmy.ansatz.install`'s registry prefers
  a namespace's `install` var over its `install!`, and this alone would skip
  the compiled-function definitions `install!` still has to do as IO."
  [ctx]
  (-> ctx
      (install-smart-constructor-lemmas)
      (ax/prove-equations simp-equations)
      (install-theorem)))

(defn install!
  "Installs the simplifier and proves `simp_correct` (a few seconds, once per
  JVM). Idempotent.

  Not a single pure `install`, unlike most of this bridge: the smart
  constructors and `simp` are compiled functions, defined through
  `ansatz.core/define-verified`, which has no ctx-parametric equivalent (see
  [[emmy.ansatz.expression/install!]]). [[install-theorems]] is pure and
  ctx-threaded; this wrapper supplies only the unavoidable IO edge around the
  compiled-function definitions sandwiched between its two phases."
  []
  (ax/install!)
  (alg/install!)
  (locking k/install-lock
    (doseq [[nm params body] smart-constructors]
      (ax/define! nm params 'Emmy.PolyExpr body))
    (ax/define! (symbol simp-name) '[e :- Emmy.PolyExpr] 'Emmy.PolyExpr simp-body)
    (k/commit! install-theorems))
  :installed)

(defn simp-poly
  "Simplifies the runtime `PolyExpr` `value` with the compiled, verified
  `Emmy.PolyExpr.simp`."
  [value]
  (install!)
  ((ax/compiled-fn simp-name) value))

(defn simplify
  "Simplifies the Emmy polynomial expression `expr` through Ansatz's verified
  `simp`, returning an Emmy expression. Its symbols other than `var` (default
  `'x`) are parameters."
  ([expr] (simplify expr 'x))
  ([expr var]
   (let [ir (ax/->ir expr)
         params (ax/params-of ir var)]
     (-> (ax/ir->value ir var params)
         (simp-poly)
         (codegen/->emmy var params)))))
