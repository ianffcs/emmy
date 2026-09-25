#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.expression
  "The verified symbolic AST: polynomial expressions as an Ansatz inductive,
  plus translation from Emmy expressions into it.

  Inside Ansatz (installed into the kernel environment by [[install!]]):

  ```
  inductive Emmy.PolyExpr
    | const (c : Int) | X | add (a b : PolyExpr) | mul (a b : PolyExpr)
    | neg (a : PolyExpr) | param (j : Nat) | frac (fnum : Int) (fden : Nat)

  Emmy.PolyExpr.num (x : Int) (ρ : Nat → Int) : PolyExpr → Int   -- numerator
  Emmy.PolyExpr.den : PolyExpr → Int                               -- denominator
  theorem Emmy.PolyExpr.den_pos : 0 < den e
  Emmy.PolyExpr.value x ρ e : Emmy.Analysis.Rational.Rep  := ⟨(num x ρ e, den e), den_pos e⟩
  ```

  `frac p q` is the rational constant `p/(q+1)`, so no denominator is zero.
  The meaning of an expression is the rational `num/den`: `den` depends only
  on the shape of the tree (the product of its fractions' denominators), and
  `value` packages both as a kernel rational (see
  [[emmy.ansatz.analysis.rational]]). Statements about values use
  `Rational.Equiv`, cross-multiplied equality of rationals.

  `X` is the distinguished variable (the one a derivative is taken with
  respect to) and `param j` is any other variable, valued by the environment
  `ρ`. Multivariate expressions are read with one chosen variable as `X` and
  the rest as parameters, numbered in sorted order.

  `num` and `den` have one equation lemma per constructor (`num_add`,
  `den_frac`, …) for use by `int_ring` (see [[emmy.ansatz.algebra]]). At
  runtime a `PolyExpr` is a tagged vector `[ctor-index field…]`, e.g.
  `x * (5 + y)` with `y` as parameter 0 is `[3 [1] [2 [0 5] [5 0]]]` and `1/2`
  is `[6 1 1]`; `num` and `den` are compiled Clojure functions, and
  [[eval-poly]] divides them exactly.

  On the Emmy side, symbolic expressions are first read into a small IR:

  ```
  [:lit r] [:var sym] [:add a b] [:sub a b] [:mul a b] [:neg a]
  ```

  Emmy's `expt` with a non-negative integer exponent, `square` and `cube`
  unfold into repeated `:mul`. Division is accepted only by a numeric literal
  (it becomes multiplication by the reciprocal). Integer literals become
  `const`, other rationals `frac`. Anything else, e.g. `sin` or
  a floating-point literal, throws `ex-info` with `:type ::unsupported`.

  The translations Emmy → IR → `PolyExpr` (here) and `PolyExpr` → Emmy
  ([[emmy.ansatz.codegen]]) are the trusted glue around the verified core, so
  they are kept small and tested by evaluating both sides."
  (:require [ansatz.core :as a]
            [ansatz.inductive :as ind]
            [ansatz.surface.ingest :as ingest]
            [clojure.set :as set]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.rational :as rat]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.install :as registry]
            [emmy.ansatz.match :as m]
            [emmy.expression :as x]))

(defn- unsupported! [msg data]
  (throw (ex-info msg (assoc data :type ::unsupported))))

(defn- exact-number? [n]
  (and (number? n) (rational? n)))

(declare ->ir*)

(defn- fold [op args]
  (reduce (fn [acc a] [op acc a]) args))

(defn- power [base n form]
  (when-not (and (integer? n) (not (neg? n)))
    (unsupported! (str "Only non-negative integer exponents are supported: " (pr-str form))
                  {:form form}))
  (if (zero? n)
    [:lit 1]
    (fold :mul (repeat n base))))

(defn- literal-value
  "Numeric value of an IR term if it is a literal (possibly negated)."
  [ir]
  (case (first ir)
    :lit (second ir)
    :neg (some-> (literal-value (second ir)) -)
    nil))

(defn- ->ir* [form]
  (cond
    (exact-number? form) [:lit form]
    (number? form) (unsupported! (str "Inexact number " form) {:form form})
    (symbol? form) [:var form]

    (seq? form)
    (let [[op & args] form
          args' (map ->ir* args)]
      (case op
        + (if (empty? args')
            [:lit 0]
            (fold :add args'))
        * (if (empty? args')
            [:lit 1]
            (fold :mul args'))
        - (case (count args')
            0 (unsupported! "Nullary -" {:form form})
            1 [:neg (first args')]
            (fold :sub args'))
        negate [:neg (first args')]
        square (power (first args') 2 form)
        cube (power (first args') 3 form)
        expt (let [[base e] args]
               (power (->ir* base) e form))
        / (let [[num & dens] args']
            (if (empty? dens)
              (let [v (literal-value num)]
                (if (and v (not (zero? v)))
                  [:lit (/ 1 v)]
                  (unsupported! (str "Non-numeric reciprocal " (pr-str form)) {:form form})))
              (reduce (fn [acc d]
                        (let [v (literal-value d)]
                          (if (and v (not (zero? v)))
                            [:mul acc [:lit (/ 1 v)]]
                            (unsupported! (str "Division by a non-numeric term " (pr-str form))
                                          {:form form}))))
                      num dens)))
        (unsupported! (str "Unsupported operation " op " in " (pr-str form))
                      {:form form :op op})))

    :else (unsupported! (str "Unsupported term " (pr-str form)) {:form form})))

(defn ->ir
  "Converts an Emmy symbolic value, or a bare expression built from Clojure
  data, into the polynomial IR."
  [expr]
  (->ir* (x/expression-of expr)))

(defn variables
  "Set of variable symbols occurring in `ir`."
  [ir]
  (case (first ir)
    :lit #{}
    :var #{(second ir)}
    (apply set/union (map variables (rest ir)))))

(defn evaluate
  "Evaluates `ir` with variables bound by `env` (symbol → number), with
  arbitrary precision."
  [ir env]
  (let [[op a b] ir]
    (case op
      :lit a
      :var (or (get env a)
               (throw (ex-info (str "Unbound variable " a) {:var a})))
      :add (+' (evaluate a env) (evaluate b env))
      :sub (-' (evaluate a env) (evaluate b env))
      :mul (*' (evaluate a env) (evaluate b env))
      :neg (-' (evaluate a env)))))

;; ## The Ansatz AST

(def ^:private ctor-index
  {:const 0 :X 1 :add 2 :mul 3 :neg 4 :param 5 :frac 6})

(def type-name "Emmy.PolyExpr")

(def num-name "Emmy.PolyExpr.num")
(def den-name "Emmy.PolyExpr.den")
(def value-name "Emmy.PolyExpr.value")
(def den-pos-name "Emmy.PolyExpr.den_pos")

(def ^:private den-body
  '(match e
     [(Emmy.PolyExpr.const c) (Int.ofNat 1)]
     [(Emmy.PolyExpr.X) (Int.ofNat 1)]
     [(Emmy.PolyExpr.add a b) (Int.mul (Emmy.PolyExpr.den a) (Emmy.PolyExpr.den b))]
     [(Emmy.PolyExpr.mul a b) (Int.mul (Emmy.PolyExpr.den a) (Emmy.PolyExpr.den b))]
     [(Emmy.PolyExpr.neg a) (Emmy.PolyExpr.den a)]
     [(Emmy.PolyExpr.param j) (Int.ofNat 1)]
     [(Emmy.PolyExpr.frac p q) (Int.ofNat (Nat.succ q))]))

(def ^:private num-body
  '(match e
     [(Emmy.PolyExpr.const c) c]
     [(Emmy.PolyExpr.X) x]
     [(Emmy.PolyExpr.add a b)
      (Int.add (Int.mul (Emmy.PolyExpr.num x rho a) (Emmy.PolyExpr.den b))
               (Int.mul (Emmy.PolyExpr.num x rho b) (Emmy.PolyExpr.den a)))]
     [(Emmy.PolyExpr.mul a b) (Int.mul (Emmy.PolyExpr.num x rho a) (Emmy.PolyExpr.num x rho b))]
     [(Emmy.PolyExpr.neg a) (Int.neg (Emmy.PolyExpr.num x rho a))]
     [(Emmy.PolyExpr.param j) (rho j)]
     [(Emmy.PolyExpr.frac p q) p]))

(def den-equations
  "Defining equations of `Emmy.PolyExpr.den`, as `[name params statement]`."
  '[[Emmy.PolyExpr.den_const [c :- Int]
     (= Int (Emmy.PolyExpr.den (Emmy.PolyExpr.const c)) (Int.ofNat 1))]
    [Emmy.PolyExpr.den_X []
     (= Int (Emmy.PolyExpr.den Emmy.PolyExpr.X) (Int.ofNat 1))]
    [Emmy.PolyExpr.den_add [a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.den (Emmy.PolyExpr.add a b))
        (Int.mul (Emmy.PolyExpr.den a) (Emmy.PolyExpr.den b)))]
    [Emmy.PolyExpr.den_mul [a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.den (Emmy.PolyExpr.mul a b))
        (Int.mul (Emmy.PolyExpr.den a) (Emmy.PolyExpr.den b)))]
    [Emmy.PolyExpr.den_neg [a :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.den (Emmy.PolyExpr.neg a)) (Emmy.PolyExpr.den a))]
    [Emmy.PolyExpr.den_param [j :- Nat]
     (= Int (Emmy.PolyExpr.den (Emmy.PolyExpr.param j)) (Int.ofNat 1))]
    [Emmy.PolyExpr.den_frac [p :- Int q :- Nat]
     (= Int (Emmy.PolyExpr.den (Emmy.PolyExpr.frac p q)) (Int.ofNat (Nat.succ q)))]])

(def num-equations
  "Defining equations of `Emmy.PolyExpr.num`, as `[name params statement]`."
  '[[Emmy.PolyExpr.num_const [x :- Int rho :- (=> Nat Int) c :- Int]
     (= Int (Emmy.PolyExpr.num x rho (Emmy.PolyExpr.const c)) c)]
    [Emmy.PolyExpr.num_X [x :- Int rho :- (=> Nat Int)]
     (= Int (Emmy.PolyExpr.num x rho Emmy.PolyExpr.X) x)]
    [Emmy.PolyExpr.num_add [x :- Int rho :- (=> Nat Int) a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.num x rho (Emmy.PolyExpr.add a b))
        (Int.add (Int.mul (Emmy.PolyExpr.num x rho a) (Emmy.PolyExpr.den b))
                 (Int.mul (Emmy.PolyExpr.num x rho b) (Emmy.PolyExpr.den a))))]
    [Emmy.PolyExpr.num_mul [x :- Int rho :- (=> Nat Int) a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.num x rho (Emmy.PolyExpr.mul a b))
        (Int.mul (Emmy.PolyExpr.num x rho a) (Emmy.PolyExpr.num x rho b)))]
    [Emmy.PolyExpr.num_neg [x :- Int rho :- (=> Nat Int) a :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.num x rho (Emmy.PolyExpr.neg a))
        (Int.neg (Emmy.PolyExpr.num x rho a)))]
    [Emmy.PolyExpr.num_param [x :- Int rho :- (=> Nat Int) j :- Nat]
     (= Int (Emmy.PolyExpr.num x rho (Emmy.PolyExpr.param j)) (rho j))]
    [Emmy.PolyExpr.num_frac [x :- Int rho :- (=> Nat Int) p :- Int q :- Nat]
     (= Int (Emmy.PolyExpr.num x rho (Emmy.PolyExpr.frac p q)) p)]])

(def semantic-equations
  "Equation lemmas of `num` and `den`, for rewriting with `int_ring`."
  (vec (concat num-equations den-equations)))

(defn prove-equations
  "Pure. Proves each `[name params statement]` by `rfl` (they hold by
  definitional unfolding) and declares it in `ctx`. Skips names already
  installed."
  [ctx equations]
  (reduce (fn [ctx [nm params prop]]
            (t/declare-theorem ctx (str nm) params prop '[(rfl)]))
          ctx equations))

(defonce ^:private compiled (atom {}))

(def ^:private runtime-ns
  "Home of the compiled verified functions, interned under their kernel names
  (e.g. `emmy.ansatz.runtime/Emmy.PolyExpr.num`). Ansatz's code generator
  refers to a constant by the symbol registered in its arity registry, so
  later definitions (like `quad` calling `eval`) link against these vars."
  (create-ns 'emmy.ansatz.runtime))

(defn- define-one! [nm params ret body]
  (when-not (and (k/installed? nm) (get @compiled (str nm)))
    (let [f   (k/quietly (a/define-verified nm params ret body))
          sym (symbol (str (ns-name runtime-ns)) (str nm))]
      (intern runtime-ns (symbol (str nm)) f)
      (swap! ingest/arity-registry update (str nm) assoc :sym sym)
      (swap! compiled assoc (str nm) f))))

(defn define!
  "Defines the verified function `nm` (kernel name) unless installed, and
  links its compiled Clojure implementation. The body may use nested
  patterns and nested matches; see [[emmy.ansatz.match]]."
  [nm params ret body]
  (when-not (and (k/installed? nm) (get @compiled (str nm)))
    (doseq [[nm params ret body] (m/desugar nm params ret body)]
      (define-one! nm params ret body))))

(defn compiled-fn
  "The compiled Clojure implementation of the verified function `nm`."
  [nm]
  (or (get @compiled (str nm))
      (throw (ex-info (str "Not installed: " nm) {:name nm}))))

(def poly-type
  "The kernel type `Emmy.PolyExpr`."
  (k/const type-name))

(defn den-term "Kernel term `den e`." [e] (t/app (k/const den-name) e))
(defn num-term "Kernel term `num x ρ e`." [x rho e] (t/app (k/const num-name) x rho e))
(defn value-term "Kernel term `value x ρ e`." [x rho e] (t/app (k/const value-name) x rho e))

(def env-type
  "The kernel type `Nat → Int` of parameter environments."
  (t/arrow (k/const "Nat") k/int-type))

(defn- install-den-pos [ctx]
  (let [pos-one '(exact (Int.ofNat_succ_pos 0))
        pos-mul '(exact (Int.mul_pos (Emmy.PolyExpr.den a) (Emmy.PolyExpr.den b) ih_a ih_b))]
    (t/declare-theorem ctx den-pos-name '[e]
      (t/forall [[e poly-type]] (rat/lt k/zero (den-term e)))
      ['(induction e)
       pos-one pos-one pos-mul pos-mul '(exact ih_a) pos-one
       '(exact (Int.ofNat_succ_pos fden))])))

(defn- install-value [ctx]
  (if (k/installed? ctx value-name)
    ctx
    (t/declare-constant ctx :def value-name
      (t/arrow k/int-type (t/arrow env-type (t/arrow poly-type (k/const "Emmy.Analysis.Rational.Rep"))))
      (t/lambda [[x k/int-type] [rho env-type] [e poly-type]]
        (rat/make-rep (num-term x rho e) (den-term e)
                      (t/app (k/const den-pos-name) e))))))

(defn- install-types
  "Declares the `Emmy.PolyExpr` inductive type into `ctx`.

  `ansatz.inductive/define-inductive` threads its environment argument and
  returns the extended one, but the vendored library also resets the
  process-global environment before returning. That's harmless as a step of
  [[install]], which the registry only runs under its lock and commits right
  after; it is not safe for inspecting-and-discarding a context."
  [ctx]
  (if (k/installed? ctx type-name)
    ctx
    (update ctx :env
      #(ind/define-inductive % type-name '[]
         '[[const [c Int]] [X []]
           [add [a Emmy.PolyExpr b Emmy.PolyExpr]]
           [mul [a Emmy.PolyExpr b Emmy.PolyExpr]]
           [neg [a Emmy.PolyExpr]]
           [param [j Nat]]
           [frac [fnum Int fden Nat]]]))))

(defn- define-semantics!
  "`num` and `den` are compiled functions: `ansatz.core/define-verified` reads
  and writes the global environment throughout, with no context-passing form."
  []
  (define! (symbol den-name) '[e :- Emmy.PolyExpr] 'Int den-body)
  (define! (symbol num-name) '[x :- Int rho :- (=> Nat Int) e :- Emmy.PolyExpr] 'Int num-body))

(defn- install-theorems [ctx]
  (-> ctx
      (prove-equations semantic-equations)
      (install-den-pos)
      (install-value)))

(def install
  "Install steps for `Emmy.PolyExpr`, `num`/`den`, their equation lemmas,
  `den_pos` and `value` (see [[emmy.ansatz.install]])."
  [(registry/pure install-types)
   (registry/io define-semantics!)
   (registry/pure install-theorems)])

(defn install!
  "Installs this namespace and its prerequisites. Idempotent."
  []
  (registry/install-through! 'emmy.ansatz.expression)
  :installed)

;; ## IR ⇄ AST values

(defn params-of
  "The parameters of `ir` with respect to `var`: its other variables, sorted."
  [ir var]
  (vec (sort (disj (variables ir) var))))

(defn ir->value
  "Converts IR into a runtime `PolyExpr`, with `var` as `X` and the symbols in
  `params` as `param 0`, `param 1`, … Integer literals become `const`, other
  rationals `p/q` (in lowest terms, `q > 0`) become `frac p (q - 1)`."
  ([ir var] (ir->value ir var (params-of ir var)))
  ([ir var params]
   (let [index (zipmap params (range))]
     (letfn [(go [[op a b]]
               (case op
                 :lit (cond (integer? a) [(ctor-index :const) a]
                            (ratio? a) [(ctor-index :frac) (numerator a) (dec (denominator a))]
                            :else (unsupported! (str "PolyExpr coefficients must be exact, got " a)
                                                {:value a}))
                 :var (cond (= a var) [(ctor-index :X)]
                            (contains? index a) [(ctor-index :param) (index a)]
                            :else (unsupported! (str "Unexpected variable " a)
                                                {:var a :var-name var :params params}))
                 :add [(ctor-index :add) (go a) (go b)]
                 :sub [(ctor-index :add) (go a) [(ctor-index :neg) (go b)]]
                 :mul [(ctor-index :mul) (go a) (go b)]
                 :neg [(ctor-index :neg) (go a)]))]
       (go ir)))))

(defn value->ir
  "Converts a runtime `PolyExpr` into IR, with `var` for `X` and `params` for
  the parameters."
  ([value var] (value->ir value var []))
  ([value var params]
   (let [[tag a b] value]
     (case (long tag)
       0 [:lit a]
       1 [:var var]
       2 [:add (value->ir a var params) (value->ir b var params)]
       3 [:mul (value->ir a var params) (value->ir b var params)]
       4 [:neg (value->ir a var params)]
       5 [:var (nth params a)]
       6 [:lit (/ a (inc b))]))))

(defn ->poly-expr
  "Reads an Emmy expression (or bare s-expression) into a runtime `PolyExpr`
  with `var` as `X`. Other symbols become parameters, numbered by their
  position in `params` (default: [[params-of]] the expression)."
  ([expr var]
   (let [ir (->ir expr)]
     (ir->value ir var (params-of ir var))))
  ([expr var params]
   (ir->value (->ir expr) var params)))

(defn eval-poly
  "The exact rational value `num/den` of the runtime `PolyExpr` `value` at the
  integer `x`, with parameter `j` valued `(nth env j)`, computed by the
  compiled `Emmy.PolyExpr.num` and `Emmy.PolyExpr.den`."
  ([value x] (eval-poly value x []))
  ([value x env]
   (/ ((compiled-fn num-name) x (fn [j] (nth env j)) value)
      ((compiled-fn den-name) value))))

(defn eval-real-poly
  "Approximate double-valued evaluation of a runtime polynomial, for
  non-integer inputs. No certified error bound is supplied; exact rational
  evaluation is [[eval-poly]]."
  ([value x] (eval-real-poly value x []))
  ([value x env]
   (let [[tag a b] value]
     (case (long tag)
       0 (double a)
       1 (double x)
       2 (+ (eval-real-poly a x env) (eval-real-poly b x env))
       3 (* (eval-real-poly a x env) (eval-real-poly b x env))
       4 (- (eval-real-poly a x env))
       5 (double (nth env a))
       6 (/ (double a) (double (inc b)))))))
