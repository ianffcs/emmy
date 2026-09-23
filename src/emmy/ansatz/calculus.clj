#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.calculus
  "Verified differentiation of polynomial expressions.

  Inside Ansatz (installed by [[install!]]):

  ```
  Emmy.PolyExpr.deriv : PolyExpr → PolyExpr                   -- ∂/∂X
  Emmy.PolyExpr.quad  : Int → Int → (Nat → Int) → PolyExpr → Int  -- remainder

  theorem Emmy.PolyExpr.deriv_correct (e : PolyExpr) (x h : Int) (ρ : Nat → Int) :
    num (x+h) ρ e · den e' = num x ρ e · den e' + h · num x ρ e' · den e + h² · quad x h ρ e
      -- where e' = deriv e
  ```

  Dividing by `den e · den e' > 0` (see `den_pos`), this says
  `f(x + h) = f(x) + h·f'(x) + h²·q` for the rational values `f = num/den` of
  `e` and `f' ` of `deriv e`, with `q = quad/(den e·den e')`: Carathéodory's
  characterization of the derivative for polynomials. `f(x + h) − f(x) −
  h·f'(x)` is divisible by `h²`, which pins `f'` down to the unique polynomial
  derivative: if `g₁`, `g₂` both satisfied it, `h·(g₁ − g₂)` would be
  divisible by `h²`, forcing `g₁ = g₂`. Rational coefficients (`frac`) are
  covered; the statement is kept in cross-multiplied form so it needs no
  division in the kernel. The parameters are held fixed by `ρ`, so for a
  multivariate expression read with variable `v` as `X`, `deriv` is the
  partial derivative `∂/∂v`; [[partial-derivative]] and [[gradient]] build on
  that.

  The theorem is proved once, by structural induction on `e`. The leaf cases
  are ring identities closed by `int_ring`; the `add`, `mul` and `neg` steps
  are separate lemmas (`deriv_correct_add`, …) proved by
  `algebra/linear-combination` from the induction hypotheses (see
  [[emmy.ansatz.algebra]]). Everything is checked by the Ansatz kernel. [[derivative]] runs the compiled `deriv`, then the verified
  `simp` of [[emmy.ansatz.simplify]], so each result is covered by
  `deriv_correct` and `simp_correct`; there is no per-result proof to run.

  ```clojure
  (derivative (fn [x] (g/* x x)))   ;; => (+ x x)
  ```"
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [clojure.walk :as walk]
            ;; symbolic arithmetic, for applying `f` to a symbol in [[derivative]]
            [emmy.abstract.number]
            [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.analysis.kernel :as t]
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
     [(Emmy.PolyExpr.param j) (Emmy.PolyExpr.const 0)]
     [(Emmy.PolyExpr.frac p q) (Emmy.PolyExpr.const 0)]))

;; ## The remainder `quad`
;;
;; Write N(a) = num x ρ a, N⁺(a) = num (x+h) ρ a, D(a) = den a,
;; N'(a) = num x ρ (deriv a), D'(a) = den (deriv a), Q(a) = quad x h ρ a. The
;; statement for `a` reads  N⁺(a)·D'(a) = N(a)·D'(a) + h·N'(a)·D(a) + h²·Q(a).
;; With A0 = N(a)D'(a), A1 = N'(a)D(a) (and B0, B1 for b), the cases are
;;
;;   add:  Q = D(b)D'(b)·Q(a) + D(a)D'(a)·Q(b)
;;   mul:  Q = D(a)D(b)·(A1B1 + A0Q(b) + Q(a)B0 + h(A1Q(b) + Q(a)B1) + h²Q(a)Q(b))
;;   neg:  Q = −Q(a),   and 0 at the leaves.

(defn- N [a] (list 'Emmy.PolyExpr.num 'x 'rho a))
(defn- D [a] (list 'Emmy.PolyExpr.den a))
(defn- N' [a] (list 'Emmy.PolyExpr.num 'x 'rho (list 'Emmy.PolyExpr.deriv a)))
(defn- D' [a] (list 'Emmy.PolyExpr.den (list 'Emmy.PolyExpr.deriv a)))
(defn- Q [a] (list 'Emmy.PolyExpr.quad 'x 'h 'rho a))
(defn- add* [& xs] (reduce #(list 'Int.add %1 %2) xs))
(defn- mul* [& xs] (reduce #(list 'Int.mul %1 %2) xs))

(def ^:private quad-add
  (add* (mul* (D 'b) (D' 'b) (Q 'a)) (mul* (D 'a) (D' 'a) (Q 'b))))

(def ^:private quad-mul
  (let [A0 (mul* (N 'a) (D' 'a)) A1 (mul* (N' 'a) (D 'a))
        B0 (mul* (N 'b) (D' 'b)) B1 (mul* (N' 'b) (D 'b))]
    (mul* (D 'a) (D 'b)
          (add* (mul* A1 B1) (mul* A0 (Q 'b)) (mul* (Q 'a) B0)
                (mul* 'h (add* (mul* A1 (Q 'b)) (mul* (Q 'a) B1)))
                (mul* 'h 'h (Q 'a) (Q 'b))))))

(def ^:private quad-arms
  ;; [constructor pattern, fields with types, right-hand side]
  [['(Emmy.PolyExpr.const c) '[c :- Int] '(Int.ofNat 0)]
   ['Emmy.PolyExpr.X [] '(Int.ofNat 0)]
   ['(Emmy.PolyExpr.add a b) '[a :- Emmy.PolyExpr b :- Emmy.PolyExpr] quad-add]
   ['(Emmy.PolyExpr.mul a b) '[a :- Emmy.PolyExpr b :- Emmy.PolyExpr] quad-mul]
   ['(Emmy.PolyExpr.neg a) '[a :- Emmy.PolyExpr] (list 'Int.neg (Q 'a))]
   ['(Emmy.PolyExpr.param j) '[j :- Nat] '(Int.ofNat 0)]
   ['(Emmy.PolyExpr.frac p q) '[p :- Int q :- Nat] '(Int.ofNat 0)]])

(def ^:private quad-body
  (apply list 'match 'e
         (for [[pat _ rhs] quad-arms]
           [(if (symbol? pat) (list pat) pat) rhs])))

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
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv (Emmy.PolyExpr.param j)) (Emmy.PolyExpr.const 0))]
    [Emmy.PolyExpr.deriv_frac [p :- Int q :- Nat]
     (= Emmy.PolyExpr (Emmy.PolyExpr.deriv (Emmy.PolyExpr.frac p q)) (Emmy.PolyExpr.const 0))]])

(def ^:private quad-equations
  (vec (for [[pat fields rhs] quad-arms
             :let [ctor (if (symbol? pat) pat (first pat))
                   tag (subs (str ctor) (count "Emmy.PolyExpr."))]]
         [(symbol (str "Emmy.PolyExpr.quad_" tag))
          (into '[x :- Int h :- Int rho :- (=> Nat Int)] fields)
          (list '= 'Int (list 'Emmy.PolyExpr.quad 'x 'h 'rho pat) rhs)])))

;; ## Kernel statements

(defn- deriv-term [e] (t/app (k/const deriv-name) e))
(defn- quad-term [x h rho e] (t/app (k/const quad-name) x h rho e))

(defn- statement
  "`N⁺(e)·D'(e) = N(e)·D'(e) + h·N'(e)·D(e) + h²·Q(e)` for kernel terms."
  [x h rho e]
  (let [e' (deriv-term e)]
    (k/eq (k/mul (ax/num-term (k/add x h) rho e) (ax/den-term e'))
          (k/add (k/add (k/mul (ax/num-term x rho e) (ax/den-term e'))
                        (k/mul h (k/mul (ax/num-term x rho e') (ax/den-term e))))
                 (k/mul (k/mul h h) (quad-term x h rho e))))))

(defn- sides
  "`[lhs rhs]` of a kernel equation."
  [eq]
  (let [[_ args] (e/get-app-fn-args eq)] [(nth args 1) (nth args 2)]))

(defn- ih-map
  "Proof map for an induction hypothesis `ih : statement x h ρ a`."
  [x h rho a ih]
  (let [[lhs rhs] (sides (statement x h rho a))]
    {:lhs lhs :rhs rhs :term ih}))

(defn- unfolded
  "The step goal for constructor `tag` applied to `a` (and `b`), with `num`,
  `den`, `deriv` and `quad` unfolded one level, spelled exactly as their
  definitions reduce so the kernel accepts it for the folded statement.
  Returns `[lhs rhs]` over the atoms num/den/quad of `a`, `b` and their
  derivatives."
  [tag x h rho a b]
  (let [xh  (k/add x h)
        Nx  #(ax/num-term x rho %)
        Nxh #(ax/num-term xh rho %)
        Dn  ax/den-term
        d   deriv-term
        Qa  (quad-term x h rho a)
        mk  (fn [numer den' nderiv denom quad]
              ;; N⁺·D' = N·D' + h·N'·D + h²·Q, given the unfolded pieces
              [(k/mul (numer Nxh) den')
               (k/add (k/add (k/mul (numer Nx) den') (k/mul h (k/mul nderiv denom)))
                      (k/mul (k/mul h h) quad))])]
    (case tag
      "add" (let [Qb (quad-term x h rho b)]
              (mk #(k/add (k/mul (% a) (Dn b)) (k/mul (% b) (Dn a)))
                  (k/mul (Dn (d a)) (Dn (d b)))
                  (k/add (k/mul (Nx (d a)) (Dn (d b))) (k/mul (Nx (d b)) (Dn (d a))))
                  (k/mul (Dn a) (Dn b))
                  (k/add (k/mul (k/mul (Dn b) (Dn (d b))) Qa)
                         (k/mul (k/mul (Dn a) (Dn (d a))) Qb))))
      "mul" (let [Qb (quad-term x h rho b)
                  A0 (k/mul (Nx a) (Dn (d a))) A1 (k/mul (Nx (d a)) (Dn a))
                  B0 (k/mul (Nx b) (Dn (d b))) B1 (k/mul (Nx (d b)) (Dn b))
                  sum (fn [& xs] (reduce k/add xs))
                  prod (fn [& xs] (reduce k/mul xs))]
              (mk #(k/mul (% a) (% b))
                  (k/mul (k/mul (Dn (d a)) (Dn b)) (k/mul (Dn a) (Dn (d b))))
                  (k/add (k/mul (k/mul (Nx (d a)) (Nx b)) (k/mul (Dn a) (Dn (d b))))
                         (k/mul (k/mul (Nx a) (Nx (d b))) (k/mul (Dn (d a)) (Dn b))))
                  (k/mul (Dn a) (Dn b))
                  (prod (Dn a) (Dn b)
                        (sum (prod A1 B1) (prod A0 Qb) (prod Qa B0)
                             (prod h (sum (prod A1 Qb) (prod Qa B1)))
                             (prod h h Qa Qb)))))
      "neg" (mk #(k/neg (% a))
                (Dn (d a))
                (k/neg (Nx (d a)))
                (Dn a)
                (k/neg Qa)))))

(defn- step-coefficients
  "Coefficients `[[c ih] …]` expressing `lhs − rhs` of the unfolded step goal
  as a combination of the induction hypotheses' differences."
  [tag x h rho a b iha ihb]
  (let [Nx  #(ax/num-term x rho %)
        Dn  ax/den-term
        d   deriv-term]
    (case tag
      "add" [[(k/mul (Dn b) (Dn (d b))) iha] [(k/mul (Dn a) (Dn (d a))) ihb]]
      "mul" (let [A0 (k/mul (Nx a) (Dn (d a))) A1 (k/mul (Nx (d a)) (Dn a))
                  Bp (k/mul (ax/num-term (k/add x h) rho b) (Dn (d b)))
                  Ae (k/add (k/add A0 (k/mul h A1)) (k/mul (k/mul h h) (quad-term x h rho a)))
                  DaDb (k/mul (Dn a) (Dn b))]
              [[(k/mul DaDb Bp) iha] [(k/mul DaDb Ae) ihb]])
      "neg" [[(k/lit -1) iha]])))

(defn- step-lemma
  "Pure. Declares `deriv_correct_<tag>` in `ctx`: the induction step for
  constructor `tag`, proved by `linear-combination` from the induction
  hypotheses."
  [ctx tag]
  (let [nm (str "Emmy.PolyExpr.deriv_correct_" tag)
        P ax/poly-type
        ctor (k/const (str "Emmy.PolyExpr." tag))]
    (if (k/installed? ctx nm)
      ctx
      (t/declare-constant ctx :thm nm
       (if (= tag "neg")
         (t/forall [[a P] [x k/int-type] [h k/int-type] [rho ax/env-type]]
           (t/arrow (statement x h rho a) (statement x h rho (t/app ctor a))))
         (t/forall [[a P] [b P] [x k/int-type] [h k/int-type] [rho ax/env-type]]
           (t/arrow (statement x h rho a)
                    (t/arrow (statement x h rho b) (statement x h rho (t/app ctor a b))))))
       (if (= tag "neg")
         (t/lambda [[a P] [x k/int-type] [h k/int-type] [rho ax/env-type]
                    [iha (statement x h rho a)]]
           (let [[lhs rhs] (unfolded tag x h rho a nil)]
             (:term (alg/linear-combination
                     lhs rhs (step-coefficients tag x h rho a nil (ih-map x h rho a iha) nil)))))
         (t/lambda [[a P] [b P] [x k/int-type] [h k/int-type] [rho ax/env-type]
                    [iha (statement x h rho a)] [ihb (statement x h rho b)]]
           (let [[lhs rhs] (unfolded tag x h rho a b)]
             (:term (alg/linear-combination
                     lhs rhs (step-coefficients tag x h rho a b
                                                (ih-map x h rho a iha)
                                                (ih-map x h rho b ihb)))))))))))

(def ^:private leaf-rules
  "Equation lemmas that close the leaf cases by `int_ring`."
  (delay (vec (concat (map first ax/semantic-equations)
                      (map first deriv-equations)
                      (map first quad-equations)))))

(defn- install-theorem [ctx]
  (let [leaf (list 'int_ring @leaf-rules)]
    (t/declare-theorem ctx theorem-name '[e x h rho]
      (t/forall [[e ax/poly-type] [x k/int-type] [h k/int-type]
                 [rho ax/env-type]]
        (statement x h rho e))
      ;; cases: const, X, add, mul, neg, param, frac
      ['(induction e) leaf leaf
       '(exact (Emmy.PolyExpr.deriv_correct_add a b x h rho ih_a ih_b))
       '(exact (Emmy.PolyExpr.deriv_correct_mul a b x h rho ih_a ih_b))
       '(exact (Emmy.PolyExpr.deriv_correct_neg a x h rho ih_a))
       leaf leaf])))

(defn install-theorems
  "Pure. Proves and declares the equation lemmas of `deriv`/`quad`, the
  induction-step lemmas and `deriv_correct` into `ctx` (see the namespace
  docstring). Assumes `deriv`/`quad` -- compiled functions, not
  ctx-threadable, see [[install!]] -- are already present in `ctx`'s
  environment.

  Deliberately not named `install`: `emmy.ansatz.install`'s registry prefers
  a namespace's `install` var over its `install!`, and this alone would skip
  the compiled-function definitions `install!` still has to do as IO."
  [ctx]
  (-> ctx
      (ax/prove-equations deriv-equations)
      (ax/prove-equations quad-equations)
      (as-> ctx (reduce step-lemma ctx ["add" "mul" "neg"]))
      (install-theorem)))

(defn install!
  "Installs `deriv`, `quad`, their equation lemmas, the induction-step lemmas
  and `deriv_correct` (see the namespace docstring). Idempotent.

  Not a single pure `install`, unlike most of this bridge: `deriv`/`quad` are
  compiled functions, defined through `ansatz.core/define-verified`, which
  has no ctx-parametric equivalent (see [[emmy.ansatz.expression/install!]]).
  [[install-theorems]] is pure and ctx-threaded; this wrapper supplies only
  the unavoidable IO edge around the two compiled-function definitions."
  []
  (ax/install!)
  (alg/install!)
  (locking k/install-lock
    (ax/define! (symbol deriv-name) '[e :- Emmy.PolyExpr] 'Emmy.PolyExpr deriv-body)
    (ax/define! (symbol quad-name) '[x :- Int h :- Int rho :- (=> Nat Int) e :- Emmy.PolyExpr]
                'Int quad-body)
    (k/commit! install-theorems))
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
  ((ax/compiled-fn deriv-name) value))

(defn- differentiate
  "`∂expr/∂var` as an Emmy expression, through Ansatz's verified `deriv` and
  `simp`; the other symbols of `expr` are parameters."
  [expr var]
  (let [ir (ax/->ir expr)
        params (ax/params-of ir var)]
    (-> (ax/ir->value ir var params)
        (deriv-poly)
        (simp/simp-poly)
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
