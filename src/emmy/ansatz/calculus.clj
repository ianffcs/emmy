#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.calculus
  "Verified differentiation of polynomial expressions.

  Inside Ansatz (installed by [[install!]]):

  ```
  Emmy.PolyExpr.deriv : PolyExpr → PolyExpr                   -- ∂/∂X
  Emmy.PolyExpr.quad  : Int → Int → (Nat → Int) → PolyExpr → Int  -- remainder

  theorem Emmy.PolyExpr.deriv_correct (e : PolyExpr) (x h : Int) (ρ : Nat → Int) :
    eval (x + h) ρ e = eval x ρ e + h * eval x ρ (deriv e) + (h * h) * quad x h ρ e
  ```

  `deriv_correct` is Carathéodory's characterization of the derivative for
  polynomials: `f(x + h) − f(x) − h·f'(x)` is divisible by `h²`, with `quad`
  giving the quotient explicitly. It pins `deriv e` down to the unique
  polynomial derivative of `eval · ρ e` in `x`: if two polynomials `g₁`, `g₂`
  both satisfied it, `h·(g₁ − g₂)` would be divisible by `h²` for all integers
  `x`, `h`, forcing `g₁ = g₂`. The parameters are held fixed by `ρ`, so for a
  multivariate expression read with variable `v` as `X`, `deriv` is the
  partial derivative `∂/∂v`; [[partial-derivative]] and [[gradient]] build on
  that.

  The theorem is proved once, by structural induction on `e`, with each case
  closed by `int_ring` (see [[emmy.ansatz.algebra]]), and checked by the
  Ansatz kernel. [[derivative]] runs the compiled `deriv`, then the verified
  `simp` of [[emmy.ansatz.simplify]], so each result is covered by
  `deriv_correct` and `simp_correct`; there is no per-result proof to run.

  ```clojure
  (derivative (fn [x] (g/* x x)))   ;; => (+ x x)
  ```"
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.name :as name]
            [clojure.walk :as walk]
            ;; symbolic arithmetic, for applying `f` to a symbol in [[derivative]]
            [emmy.abstract.number]
            [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.codegen :as codegen]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]
            [emmy.ansatz.simplify :as simp]
            [emmy.expression :as x]
            [emmy.generic :as g]
            [emmy.structure :as s]))

(def deriv-name "Emmy.PolyExpr.deriv")
(def quad-name "Emmy.PolyExpr.quad")
(def theorem-name "Emmy.PolyExpr.deriv_correct")

(def ^:private deriv-body
  '(match e
     [(Emmy.PolyExpr.const c) (Emmy.PolyExpr.const 0)]
     [(Emmy.PolyExpr.X) (Emmy.PolyExpr.const 1)]
     [(Emmy.PolyExpr.add a b)
      (Emmy.PolyExpr.add (Emmy.PolyExpr.deriv a) (Emmy.PolyExpr.deriv b))]
     [(Emmy.PolyExpr.mul a b)
      (Emmy.PolyExpr.add (Emmy.PolyExpr.mul (Emmy.PolyExpr.deriv a) b)
                         (Emmy.PolyExpr.mul a (Emmy.PolyExpr.deriv b)))]
     [(Emmy.PolyExpr.neg a) (Emmy.PolyExpr.neg (Emmy.PolyExpr.deriv a))]
     [(Emmy.PolyExpr.param j) (Emmy.PolyExpr.const 0)]))

;; With A = eval x ρ a, A' = eval x ρ (deriv a), Qa = quad x h ρ a (and likewise
;; for b), the product case expands as
;;
;;   (A + hA' + h²Qa)(B + hB' + h²Qb)
;;     = AB + h(A'B + AB') + h²(A'B' + QaB + AQb + h(A'Qb + QaB') + h²QaQb)

(def ^:private quad-mul
  '(Int.add
    (Int.add
     (Int.add (Int.mul (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.deriv a))
                       (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.deriv b)))
              (Int.mul (Emmy.PolyExpr.quad x h rho a) (Emmy.PolyExpr.eval x rho b)))
     (Int.mul (Emmy.PolyExpr.eval x rho a) (Emmy.PolyExpr.quad x h rho b)))
    (Int.add
     (Int.mul h (Int.add (Int.mul (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.deriv a))
                                  (Emmy.PolyExpr.quad x h rho b))
                         (Int.mul (Emmy.PolyExpr.quad x h rho a)
                                  (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.deriv b)))))
     (Int.mul (Int.mul h h) (Int.mul (Emmy.PolyExpr.quad x h rho a) (Emmy.PolyExpr.quad x h rho b))))))

(def ^:private quad-body
  (list 'match 'e
        '[(Emmy.PolyExpr.const c) (Int.ofNat 0)]
        '[(Emmy.PolyExpr.X) (Int.ofNat 0)]
        '[(Emmy.PolyExpr.add a b) (Int.add (Emmy.PolyExpr.quad x h rho a) (Emmy.PolyExpr.quad x h rho b))]
        ['(Emmy.PolyExpr.mul a b) quad-mul]
        '[(Emmy.PolyExpr.neg a) (Int.neg (Emmy.PolyExpr.quad x h rho a))]
        '[(Emmy.PolyExpr.param j) (Int.ofNat 0)]))

(def ^:private deriv-equations
  '[[Emmy.PolyExpr.deriv_const [c :- Int]
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv (Emmy.PolyExpr.const c)) (Emmy.PolyExpr.const 0))]
    [Emmy.PolyExpr.deriv_X []
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv Emmy.PolyExpr.X) (Emmy.PolyExpr.const 1))]
    [Emmy.PolyExpr.deriv_add [a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv (Emmy.PolyExpr.add a b))
        (Emmy.PolyExpr.add (Emmy.PolyExpr.deriv a) (Emmy.PolyExpr.deriv b)))]
    [Emmy.PolyExpr.deriv_mul [a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv (Emmy.PolyExpr.mul a b))
        (Emmy.PolyExpr.add (Emmy.PolyExpr.mul (Emmy.PolyExpr.deriv a) b)
                           (Emmy.PolyExpr.mul a (Emmy.PolyExpr.deriv b))))]
    [Emmy.PolyExpr.deriv_neg [a :- Emmy.PolyExpr]
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv (Emmy.PolyExpr.neg a))
        (Emmy.PolyExpr.neg (Emmy.PolyExpr.deriv a)))]
    [Emmy.PolyExpr.deriv_param [j :- Nat]
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv (Emmy.PolyExpr.param j)) (Emmy.PolyExpr.const 0))]])

(def ^:private quad-equations
  [['Emmy.PolyExpr.quad_const '[x :- Int h :- Int rho :- (=> Nat Int) c :- Int]
    '(= Int (Emmy.PolyExpr.quad x h rho (Emmy.PolyExpr.const c)) (Int.ofNat 0))]
   ['Emmy.PolyExpr.quad_X '[x :- Int h :- Int rho :- (=> Nat Int)]
    '(= Int (Emmy.PolyExpr.quad x h rho Emmy.PolyExpr.X) (Int.ofNat 0))]
   ['Emmy.PolyExpr.quad_add '[x :- Int h :- Int rho :- (=> Nat Int) a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
    '(= Int (Emmy.PolyExpr.quad x h rho (Emmy.PolyExpr.add a b))
        (Int.add (Emmy.PolyExpr.quad x h rho a) (Emmy.PolyExpr.quad x h rho b)))]
   ['Emmy.PolyExpr.quad_mul '[x :- Int h :- Int rho :- (=> Nat Int) a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
    (list '= 'Int '(Emmy.PolyExpr.quad x h rho (Emmy.PolyExpr.mul a b)) quad-mul)]
   ['Emmy.PolyExpr.quad_neg '[x :- Int h :- Int rho :- (=> Nat Int) a :- Emmy.PolyExpr]
    '(= Int (Emmy.PolyExpr.quad x h rho (Emmy.PolyExpr.neg a))
        (Int.neg (Emmy.PolyExpr.quad x h rho a)))]
   ['Emmy.PolyExpr.quad_param '[x :- Int h :- Int rho :- (=> Nat Int) j :- Nat]
    '(= Int (Emmy.PolyExpr.quad x h rho (Emmy.PolyExpr.param j)) (Int.ofNat 0))]])

(def ^:private theorem-statement
  '(= Int
      (Emmy.PolyExpr.eval (Int.add x h) rho e)
      (Int.add (Int.add (Emmy.PolyExpr.eval x rho e)
                        (Int.mul h (Emmy.PolyExpr.eval x rho (Emmy.PolyExpr.deriv e))))
               (Int.mul (Int.mul h h) (Emmy.PolyExpr.quad x h rho e)))))

(def ^:private theorem-proof
  ;; `induction` produces the cases in constructor order: const, X, add, mul,
  ;; neg, param. Each is closed by rewriting with the defining equations (and the
  ;; induction hypotheses) and normalizing in the commutative ring Int.
  (let [eqs (map first (concat ax/eval-equations deriv-equations quad-equations))
        case (fn [& ihs] (list 'int_ring (vec (concat eqs ihs))))]
    ['(induction e)
     (case)
     (case)
     (case 'ih_a 'ih_b)
     (case 'ih_a 'ih_b)
     (case 'ih_a)
     (case)]))

(defn install!
  "Installs `deriv`, `quad`, their equation lemmas and `deriv_correct` into
  the Ansatz environment, proving the theorem (≈1s, once per JVM).
  Idempotent."
  []
  (ax/install!)
  (alg/install!)
  (locking k/install-lock
    (ax/define! (symbol deriv-name) '[e :- Emmy.PolyExpr] 'Emmy.PolyExpr deriv-body)
    (ax/define! (symbol quad-name) '[x :- Int h :- Int rho :- (=> Nat Int) e :- Emmy.PolyExpr] 'Int quad-body)
    (ax/prove-equations! deriv-equations)
    (ax/prove-equations! quad-equations)
    (when-not (k/installed? theorem-name)
      (k/quietly
       (a/prove-theorem (symbol theorem-name)
                        '[e :- Emmy.PolyExpr x :- Int h :- Int rho :- (=> Nat Int)]
                        theorem-statement theorem-proof))))
  :installed)

(defn theorem
  "The kernel statement of `Emmy.PolyExpr.deriv_correct`, rendered as a
  string. Installs it first if needed."
  []
  (install!)
  (-> (env/lookup (k/env) (name/from-string theorem-name))
      env/ci-type
      k/->string))

(defn deriv-poly
  "Differentiates the runtime `PolyExpr` `value` with the compiled, verified
  `Emmy.PolyExpr.deriv`."
  [value]
  (install!)
  (if (map? value)
    {:numerator ((ax/compiled-fn deriv-name) (:numerator value))
     :denominator (:denominator value)}
    ((ax/compiled-fn deriv-name) value)))

(defn- differentiate
  "`∂expr/∂var` as an Emmy expression, through Ansatz's verified `deriv` and
  `simp`; the other symbols of `expr` are parameters."
  [expr var]
  (let [ir (ax/->ir expr)
        params (ax/params-of ir var)]
    (-> (ax/ir->value ir var params)
        (deriv-poly)
        (#(if (map? %) (update % :numerator simp/simp-poly) (simp/simp-poly %)))
        (codegen/->emmy var params))))

(defn derivative
  "Differentiates `f` with respect to `var` (default `'x`) through Ansatz,
  simplifies the result with Ansatz's verified `simp`, and returns it as an
  Emmy expression. Emmy's `simplify` can canonicalize it further.

  `f` is either a Clojure function of one argument, applied to `var`
  symbolically, or an Emmy expression. Symbols other than `var` are treated
  as constants, so this is the partial derivative `∂f/∂var`. `f` must be a
  polynomial with integer coefficients; anything else throws `ex-info` with
  `:type :emmy.ansatz.expression/unsupported`."
  ([f] (derivative f 'x))
  ([f var]
   (differentiate (if (fn? f) (f var) f) var)))

(defn- arg-symbols [n]
  (mapv #(symbol (str "x" %)) (range n)))

(defn- evaluator
  "A function of `n` arguments that evaluates `expr`, an expression in
  [[arg-symbols]], at its arguments. Symbolic arguments are substituted; the
  result is an Emmy expression."
  [expr n]
  (fn [& args]
    (when-not (= n (count args))
      (throw (ex-info (str "Expected " n " arguments, got " (count args)) {:args args})))
    (let [form (x/expression-of expr)
          smap (zipmap (arg-symbols n) (map x/expression-of args))]
      (g/simplify (x/make-literal ::x/numeric (walk/postwalk-replace smap form))))))

(defn partial-derivative
  "Returns the partial derivative of `f`, a Clojure function of `n` arguments
  (default 1), in its argument `i`, computed through Ansatz: a function of `n`
  arguments, like `((emmy.calculus.derivative/partial i) f)`."
  ([f i] (partial-derivative f i 1))
  ([f i n]
   (let [syms (arg-symbols n)]
     (evaluator (differentiate (apply f syms) (syms i)) n))))

(defn gradient
  "Returns the gradient of `f`, a Clojure function of `n` arguments, computed
  through Ansatz: a function of `n` arguments returning a `down` of partial
  derivatives, like `(emmy.calculus.derivative/D f)`."
  [f n]
  (let [syms (arg-symbols n)
        expr (apply f syms)
        partials (mapv #(evaluator (differentiate expr %) n) syms)]
    (fn [& args]
      (apply s/down (map #(apply % args) partials)))))
