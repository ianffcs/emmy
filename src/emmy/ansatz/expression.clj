#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.expression
  "The verified symbolic AST: polynomial expressions as an Ansatz inductive,
  plus translation from Emmy expressions into it.

  Inside Ansatz (installed into the kernel environment by [[install!]]):

  ```
  inductive Emmy.PolyExpr
    | const (c : Int) | X | add (a b : PolyExpr) | mul (a b : PolyExpr) | neg (a : PolyExpr)

  Emmy.PolyExpr.eval (x : Int) : PolyExpr → Int      -- denotation
  ```

  with one equation lemma per constructor (`Emmy.PolyExpr.eval_add`, …) for
  use by `int_ring` (see [[emmy.ansatz.algebra]]). At runtime a `PolyExpr` is a
  tagged vector `[ctor-index field…]`, e.g. `x * (5 + x)` is
  `[3 [1] [2 [0 5] [1]]]`, and `eval` is a compiled Clojure function.

  On the Emmy side, symbolic expressions are first read into a small IR:

  ```
  [:lit r] [:var sym] [:add a b] [:sub a b] [:mul a b] [:neg a]
  ```

  Emmy's `expt` with a non-negative integer exponent, `square` and `cube`
  unfold into repeated `:mul`. Division is accepted only by a numeric literal
  (it becomes multiplication by the reciprocal). Anything else, e.g. `sin` or
  a floating-point literal, throws `ex-info` with `:type ::unsupported`.

  The translations Emmy → IR → `PolyExpr` (here) and `PolyExpr` → Emmy
  ([[emmy.ansatz.codegen]]) are the trusted glue around the verified core, so
  they are kept small and tested by evaluating both sides."
  (:require [ansatz.core :as a]
            [ansatz.surface.ingest :as ingest]
            [clojure.set :as set]
            [emmy.ansatz.core :as k]
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
        + (if (empty? args') [:lit 0] (fold :add args'))
        * (if (empty? args') [:lit 1] (fold :mul args'))
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
  {:const 0 :X 1 :add 2 :mul 3 :neg 4})

(def type-name "Emmy.PolyExpr")

(def ^:private eval-name "Emmy.PolyExpr.eval")

(def ^:private eval-body
  '(match e
     [(Emmy.PolyExpr.const c) c]
     [(Emmy.PolyExpr.X) x]
     [(Emmy.PolyExpr.add a b) (Int.add (Emmy.PolyExpr.eval x a) (Emmy.PolyExpr.eval x b))]
     [(Emmy.PolyExpr.mul a b) (Int.mul (Emmy.PolyExpr.eval x a) (Emmy.PolyExpr.eval x b))]
     [(Emmy.PolyExpr.neg a) (Int.neg (Emmy.PolyExpr.eval x a))]))

(def eval-equations
  "Defining equations of `Emmy.PolyExpr.eval`, as `[name params statement]`."
  '[[Emmy.PolyExpr.eval_const [x :- Int c :- Int]
     (= Int (Emmy.PolyExpr.eval x (Emmy.PolyExpr.const c)) c)]
    [Emmy.PolyExpr.eval_X [x :- Int]
     (= Int (Emmy.PolyExpr.eval x Emmy.PolyExpr.X) x)]
    [Emmy.PolyExpr.eval_add [x :- Int a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.eval x (Emmy.PolyExpr.add a b))
        (Int.add (Emmy.PolyExpr.eval x a) (Emmy.PolyExpr.eval x b)))]
    [Emmy.PolyExpr.eval_mul [x :- Int a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.eval x (Emmy.PolyExpr.mul a b))
        (Int.mul (Emmy.PolyExpr.eval x a) (Emmy.PolyExpr.eval x b)))]
    [Emmy.PolyExpr.eval_neg [x :- Int a :- Emmy.PolyExpr]
     (= Int (Emmy.PolyExpr.eval x (Emmy.PolyExpr.neg a))
        (Int.neg (Emmy.PolyExpr.eval x a)))]])

(defn prove-equations!
  "Proves each `[name params statement]` by `rfl` (they hold by definitional
  unfolding) and installs it. Skips names that are already installed."
  [equations]
  (doseq [[nm params prop] equations
          :when (not (k/installed? nm))]
    (k/quietly (a/prove-theorem nm params prop '[(rfl)]))))

(defonce ^:private compiled (atom {}))

(def ^:private runtime-ns
  "Home of the compiled verified functions, interned under their kernel names
  (e.g. `emmy.ansatz.runtime/Emmy.PolyExpr.eval`). Ansatz's code generator
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

(defn install!
  "Installs `Emmy.PolyExpr`, its `eval` and eval's equation lemmas into the
  Ansatz environment. Idempotent."
  []
  (k/ensure-init!)
  (locking k/install-lock
    (when-not (k/installed? type-name)
      (k/quietly
       (eval '(ansatz.core/inductive Emmy.PolyExpr []
                                     (const [c Int])
                                     (X)
                                     (add [a Emmy.PolyExpr] [b Emmy.PolyExpr])
                                     (mul [a Emmy.PolyExpr] [b Emmy.PolyExpr])
                                     (neg [a Emmy.PolyExpr])))))
    (define! (symbol eval-name) '[x :- Int e :- Emmy.PolyExpr] 'Int eval-body)
    (prove-equations! eval-equations))
  :installed)

;; ## IR ⇄ AST values

(defn ir->value
  "Converts IR over the single variable `var` into a runtime `PolyExpr`."
  [ir var]
  (let [[op a b] ir]
    (case op
      :lit (if (integer? a)
             [(ctor-index :const) a]
             (unsupported! (str "PolyExpr coefficients are integers, got " a) {:value a}))
      :var (if (= a var)
             [(ctor-index :X)]
             (unsupported! (str "Unexpected variable " a " (expected " var ")")
                           {:var a :expected var}))
      :add [(ctor-index :add) (ir->value a var) (ir->value b var)]
      :sub [(ctor-index :add) (ir->value a var) [(ctor-index :neg) (ir->value b var)]]
      :mul [(ctor-index :mul) (ir->value a var) (ir->value b var)]
      :neg [(ctor-index :neg) (ir->value a var)])))

(defn value->ir
  "Converts a runtime `PolyExpr` into IR, with `var` for the variable."
  [value var]
  (let [[tag a b] value]
    (case (long tag)
      0 [:lit a]
      1 [:var var]
      2 [:add (value->ir a var) (value->ir b var)]
      3 [:mul (value->ir a var) (value->ir b var)]
      4 [:neg (value->ir a var)])))

(defn ->poly-expr
  "Reads an Emmy expression (or bare s-expression) in the single variable
  `var` into a runtime `PolyExpr`."
  [expr var]
  (ir->value (->ir expr) var))

(defn eval-poly
  "Evaluates the runtime `PolyExpr` `value` at the integer `x` using the
  compiled `Emmy.PolyExpr.eval`."
  [value x]
  ((compiled-fn eval-name) x value))
