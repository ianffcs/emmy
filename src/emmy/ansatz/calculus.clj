#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.calculus
  "Verified differentiation of polynomial expressions.

  Inside Ansatz (installed by [[install!]]):

  ```
  Emmy.PolyExpr.deriv : PolyExpr → PolyExpr          -- sum and product rules
  Emmy.PolyExpr.quad  : Int → Int → PolyExpr → Int   -- remainder witness

  theorem Emmy.PolyExpr.deriv_correct (e : PolyExpr) (x h : Int) :
    eval (x + h) e = eval x e + h * eval x (deriv e) + (h * h) * quad x h e
  ```

  `deriv_correct` is Carathéodory's characterization of the derivative for
  polynomials: `f(x + h) − f(x) − h·f'(x)` is divisible by `h²`, with `quad`
  giving the quotient explicitly. It pins `deriv e` down to the unique
  polynomial derivative of `eval · e`: if two polynomials `g₁`, `g₂` both
  satisfied it, `h·(g₁ − g₂)` would be divisible by `h²` for all integers `x`,
  `h`, forcing `g₁ = g₂`.

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
            ;; symbolic arithmetic, for applying `f` to a symbol in [[derivative]]
            [emmy.abstract.number]
            [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.codegen :as codegen]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]
            [emmy.ansatz.simplify :as simp]))

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
     [(Emmy.PolyExpr.neg a) (Emmy.PolyExpr.neg (Emmy.PolyExpr.deriv a))]))

;; With A = eval x a, A' = eval x (deriv a), Qa = quad x h a (and likewise
;; for b), the product case expands as
;;
;;   (A + hA' + h²Qa)(B + hB' + h²Qb)
;;     = AB + h(A'B + AB') + h²(A'B' + QaB + AQb + h(A'Qb + QaB') + h²QaQb)

(def ^:private quad-mul
  '(Int.add
    (Int.add
     (Int.add (Int.mul (Emmy.PolyExpr.eval x (Emmy.PolyExpr.deriv a))
                       (Emmy.PolyExpr.eval x (Emmy.PolyExpr.deriv b)))
              (Int.mul (Emmy.PolyExpr.quad x h a) (Emmy.PolyExpr.eval x b)))
     (Int.mul (Emmy.PolyExpr.eval x a) (Emmy.PolyExpr.quad x h b)))
    (Int.add
     (Int.mul h (Int.add (Int.mul (Emmy.PolyExpr.eval x (Emmy.PolyExpr.deriv a))
                                  (Emmy.PolyExpr.quad x h b))
                         (Int.mul (Emmy.PolyExpr.quad x h a)
                                  (Emmy.PolyExpr.eval x (Emmy.PolyExpr.deriv b)))))
     (Int.mul (Int.mul h h) (Int.mul (Emmy.PolyExpr.quad x h a) (Emmy.PolyExpr.quad x h b))))))

(def ^:private quad-body
  (list 'match 'e
        '[(Emmy.PolyExpr.const c) (Int.ofNat 0)]
        '[(Emmy.PolyExpr.X) (Int.ofNat 0)]
        '[(Emmy.PolyExpr.add a b) (Int.add (Emmy.PolyExpr.quad x h a) (Emmy.PolyExpr.quad x h b))]
        ['(Emmy.PolyExpr.mul a b) quad-mul]
        '[(Emmy.PolyExpr.neg a) (Int.neg (Emmy.PolyExpr.quad x h a))]))

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
        (Emmy.PolyExpr.neg (Emmy.PolyExpr.deriv a)))]])

(def ^:private quad-equations
  [['Emmy.PolyExpr.quad_const '[x :- Int h :- Int c :- Int]
    '(= Int (Emmy.PolyExpr.quad x h (Emmy.PolyExpr.const c)) (Int.ofNat 0))]
   ['Emmy.PolyExpr.quad_X '[x :- Int h :- Int]
    '(= Int (Emmy.PolyExpr.quad x h Emmy.PolyExpr.X) (Int.ofNat 0))]
   ['Emmy.PolyExpr.quad_add '[x :- Int h :- Int a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
    '(= Int (Emmy.PolyExpr.quad x h (Emmy.PolyExpr.add a b))
        (Int.add (Emmy.PolyExpr.quad x h a) (Emmy.PolyExpr.quad x h b)))]
   ['Emmy.PolyExpr.quad_mul '[x :- Int h :- Int a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
    (list '= 'Int '(Emmy.PolyExpr.quad x h (Emmy.PolyExpr.mul a b)) quad-mul)]
   ['Emmy.PolyExpr.quad_neg '[x :- Int h :- Int a :- Emmy.PolyExpr]
    '(= Int (Emmy.PolyExpr.quad x h (Emmy.PolyExpr.neg a))
        (Int.neg (Emmy.PolyExpr.quad x h a)))]])

(def ^:private theorem-statement
  '(= Int
      (Emmy.PolyExpr.eval (Int.add x h) e)
      (Int.add (Int.add (Emmy.PolyExpr.eval x e)
                        (Int.mul h (Emmy.PolyExpr.eval x (Emmy.PolyExpr.deriv e))))
               (Int.mul (Int.mul h h) (Emmy.PolyExpr.quad x h e)))))

(def ^:private theorem-proof
  ;; `induction` produces the cases in constructor order: const, X, add, mul,
  ;; neg. Each is closed by rewriting with the defining equations (and the
  ;; induction hypotheses) and normalizing in the commutative ring Int.
  (let [eqs (map first (concat ax/eval-equations deriv-equations quad-equations))
        case (fn [& ihs] (list 'int_ring (vec (concat eqs ihs))))]
    ['(induction e)
     (case)
     (case)
     (case 'ih_a 'ih_b)
     (case 'ih_a 'ih_b)
     (case 'ih_a)]))

(defn install!
  "Installs `deriv`, `quad`, their equation lemmas and `deriv_correct` into
  the Ansatz environment, proving the theorem (≈1s, once per JVM).
  Idempotent."
  []
  (ax/install!)
  (alg/install!)
  (locking k/install-lock
    (ax/define! (symbol deriv-name) '[e :- Emmy.PolyExpr] 'Emmy.PolyExpr deriv-body)
    (ax/define! (symbol quad-name) '[x :- Int h :- Int e :- Emmy.PolyExpr] 'Int quad-body)
    (ax/prove-equations! deriv-equations)
    (ax/prove-equations! quad-equations)
    (when-not (k/installed? theorem-name)
      (k/quietly
       (a/prove-theorem (symbol theorem-name) '[e :- Emmy.PolyExpr x :- Int h :- Int]
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
  ((ax/compiled-fn deriv-name) value))

(defn derivative
  "Differentiates `f` with respect to `var` (default `'x`) through Ansatz,
  simplifies the result with Ansatz's verified `simp`, and returns it as an
  Emmy expression. Emmy's `simplify` can canonicalize it further.

  `f` is either a Clojure function of one argument, applied to `var`
  symbolically, or an Emmy expression in `var`. It must be a polynomial with
  integer coefficients; anything else throws `ex-info` with
  `:type :emmy.ansatz.expression/unsupported`."
  ([f] (derivative f 'x))
  ([f var]
   (let [expr (if (fn? f) (f var) f)]
     (-> (ax/->poly-expr expr var)
         (deriv-poly)
         (simp/simp-poly)
         (codegen/->emmy var)))))
