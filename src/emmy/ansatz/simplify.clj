#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.simplify
  "Verified simplification of polynomial expressions.

  Inside Ansatz (installed by [[install!]]):

  ```
  Emmy.PolyExpr.mkAdd, mkMul : PolyExpr → PolyExpr → PolyExpr   -- smart constructors
  Emmy.PolyExpr.mkNeg        : PolyExpr → PolyExpr
  Emmy.PolyExpr.simp         : PolyExpr → PolyExpr             -- bottom-up rebuild

  theorem Emmy.PolyExpr.simp_correct (e : PolyExpr) (x : Int) (ρ : Nat → Int) :
    eval x ρ (simp e) = eval x ρ e
  ```

  The smart constructors drop additive zeros and multiplicative ones,
  annihilate with zero, fold constant arithmetic and cancel double negation.
  Each has its own correctness lemma (e.g. `mkAdd_correct : eval x ρ (mkAdd p q)
  = eval x ρ p + eval x ρ q`), proved by `int_ring_split`, which case-splits on
  the constructors and integer literals the definition inspects. `simp_correct`
  then follows by induction.

  `simp` is deliberately local. It doesn't collect like terms or reorder
  (`x + x` stays as it is); that is Emmy's canonical simplifier's job
  downstream.

  The smart constructors are written with nested patterns such as
  `(Emmy.PolyExpr.const (Int.ofNat 0))`; [[emmy.ansatz.match]] compiles them
  into shapes Ansatz can elaborate, and the `Int.rec` lowering registered by
  [[emmy.ansatz.core/ensure-init!]] runs them natively."
  (:require [ansatz.core :as a]
            [emmy.ansatz.algebra :as alg]
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
       [(Emmy.PolyExpr.neg a) a]
       [_ (Emmy.PolyExpr.neg p)])]])

(def ^:private eval-rules
  (mapv first ax/eval-equations))

(def ^:private smart-constructor-lemmas
  ;; [name params statement definition-to-unfold]
  [['Emmy.PolyExpr.mkAdd_correct '[p :- Emmy.PolyExpr q :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
    '(= Int (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.mkAdd p q))
        (Int.add (Emmy.PolyExpr.eval x rho p) (Emmy.PolyExpr.eval x rho q)))
    '[Emmy.PolyExpr.mkAdd]]
   ['Emmy.PolyExpr.mkMul_correct '[p :- Emmy.PolyExpr q :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
    '(= Int (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.mkMul p q))
        (Int.mul (Emmy.PolyExpr.eval x rho p) (Emmy.PolyExpr.eval x rho q)))
    '[Emmy.PolyExpr.mkMul]]
   ['Emmy.PolyExpr.mkNeg_correct '[p :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
    '(= Int (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.mkNeg p))
        (Int.neg (Emmy.PolyExpr.eval x rho p)))
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
     [(Emmy.PolyExpr.param j) (Emmy.PolyExpr.param j)]))

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
     (= Emmy.PolyExpr (Emmy.PolyExpr.simp (Emmy.PolyExpr.param j)) (Emmy.PolyExpr.param j))]])

(def ^:private theorem-proof
  ;; Cases in constructor order: const, X, add, mul, neg, param.
  (let [rules (vec (concat (map first simp-equations)
                           (map first smart-constructor-lemmas)
                           eval-rules))
        case (fn [& ihs] (list 'int_ring (into rules ihs)))]
    ['(induction e)
     (case)
     (case)
     (case 'ih_a 'ih_b)
     (case 'ih_a 'ih_b)
     (case 'ih_a)
     (case)]))

(defn install!
  "Installs the simplifier and proves `simp_correct` (≈2s, once per JVM).
  Idempotent."
  []
  (ax/install!)
  (alg/install!)
  (locking k/install-lock
    (doseq [[nm params body] smart-constructors]
      (ax/define! nm params 'Emmy.PolyExpr body))
    (doseq [[nm params prop unfold] smart-constructor-lemmas
            :when (not (k/installed? nm))]
      (k/quietly
       (a/prove-theorem nm params prop
                        [(list 'int_ring_split (into unfold eval-rules))])))
    (ax/define! (symbol simp-name) '[e :- Emmy.PolyExpr] 'Emmy.PolyExpr simp-body)
    (ax/prove-equations! simp-equations)
    (when-not (k/installed? theorem-name)
      (k/quietly
       (a/prove-theorem (symbol theorem-name) '[e :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
                        '(= Int (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.simp e))
                            (Emmy.PolyExpr.eval x rho e))
                        theorem-proof))))
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
