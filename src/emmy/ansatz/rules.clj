#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.rules
  "Emmy-style rewrite rules, compiled into verified Ansatz transformations.

  Rules use the syntax of [[emmy.pattern.rule]]:

  ```clojure
  (defruleset units
    (+ 0 ?a) => ?a
    (* 1 ?a) => ?a
    (* (? ?c integer?) (? ?d integer?)) => (* ?c ?d))
  ```

  A rule set named `units` becomes, inside Ansatz:

  ```
  Emmy.Rules.units.step : PolyExpr → PolyExpr   -- the first matching rule, else e
  Emmy.Rules.units.simp : PolyExpr → PolyExpr   -- step, applied bottom-up

  theorem Emmy.Rules.units.rule_<i>     -- each rule preserves eval
  theorem Emmy.Rules.units.step_correct : eval x ρ (step e) = eval x ρ e
  theorem Emmy.Rules.units.simp_correct : eval x ρ (simp e) = eval x ρ e
  ```

  An unsound rule is rejected when the set is defined: its `rule_<i>` lemma
  fails to prove, and the error names the rule. Everything is checked by the
  Ansatz kernel; [[simplifier]] iterates the compiled, verified `simp` to a
  fixpoint (each iteration preserves the value, so the result does too).

  ### Pattern language

  Patterns and skeletons are Emmy expressions over the single variable `x`:

  - `?a` matches any subexpression (`_` matches without binding);
  - `(? ?c integer?)` matches an integer constant and binds its value
    (`int?` and `v/integral?` are accepted as the predicate too);
  - integer literals and `x` match themselves;
  - `(+ a b)`, `(* a b)`, `(- a)` and `(- a b)` (read as `a + (-b)`) match
    the corresponding nodes. Operators are binary, as in `Emmy.PolyExpr`.

  In a skeleton, arithmetic whose leaves are all integers or
  integer-bound variables is computed (`(* ?c ?d)` above folds the constants).
  Each variable may appear only once in a pattern, and segment variables
  (`??a`) are not supported."
  (:require [ansatz.core :as a]
            [clojure.walk :as walk]
            [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.codegen :as codegen]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]
            [emmy.pattern.syntax :as ps]))

(defn- unsupported! [msg data]
  (throw (ex-info (str "ruleset: " msg) (assoc data :type ::unsupported))))

;; ## Patterns

(defn- var-sym
  "The Ansatz binder for the pattern variable `?name` or `(? ?name …)`."
  [pattern]
  (let [v (name (ps/variable-name pattern))]
    (symbol (str "v_" (if (= \? (first v)) (subs v 1) v)))))

(def ^:private int-predicates
  '#{integer? int? v/integral? emmy.value/integral?})

(defn- int-restriction? [pattern]
  (and (ps/restricted? pattern)
       (= 3 (count pattern))
       (contains? int-predicates (nth pattern 2))))

(defn- int-pattern
  "Ansatz pattern for the integer literal `n`."
  [n]
  (if (neg? n)
    (list 'Int.negSucc (- (- n) 1))
    (list 'Int.ofNat n)))

(defn- compile-pattern
  "Ansatz pattern for the Emmy pattern `p`. Records bound variables in the
  `vars` atom as `[sym :poly|:int]`."
  [p vars]
  (letfn [(bind! [sym kind]
            (when (some #(= sym (first %)) @vars)
              (unsupported! (str "non-linear patterns are not supported (" sym " occurs twice)") {:pattern p}))
            (swap! vars conj [sym kind])
            sym)
          (go [p]
            (cond
              (ps/wildcard? p) '_
              (ps/segment? p) (unsupported! "segment variables are not supported" {:pattern p})
              (and (ps/binding? p) (ps/restricted? p))
              (if (int-restriction? p)
                (list 'Emmy.PolyExpr.const
                      (if (ps/wildcard? (ps/variable-name p)) '_ (bind! (var-sym p) :int)))
                (unsupported! (str "only the integer? restriction is supported: " (pr-str p))
                              {:pattern p}))
              (ps/binding? p) (bind! (var-sym p) :poly)
              (integer? p) (list 'Emmy.PolyExpr.const (int-pattern p))
              (= 'x p) '(Emmy.PolyExpr.X)
              (seq? p)
              (let [[op & args] p]
                (case [op (count args)]
                  [+ 2] (list 'Emmy.PolyExpr.add (go (first args)) (go (second args)))
                  [* 2] (list 'Emmy.PolyExpr.mul (go (first args)) (go (second args)))
                  [- 1] (list 'Emmy.PolyExpr.neg (go (first args)))
                  [- 2] (list 'Emmy.PolyExpr.add (go (first args))
                              (list 'Emmy.PolyExpr.neg (go (second args))))
                  (unsupported! (str "unsupported pattern " (pr-str p)) {:pattern p})))
              :else (unsupported! (str "unsupported pattern " (pr-str p)) {:pattern p})))]
    (go p)))

(defn- compile-skeleton
  "Ansatz term for the Emmy skeleton `s`, given the pattern's `vars`."
  [s vars]
  (let [kinds (into {} vars)
        lookup (fn [v]
                 (let [sym (var-sym v)]
                   (or (some-> (kinds sym) (vector sym))
                       (unsupported! (str "unbound variable in skeleton: " v) {:skeleton s}))))
        int-valued? (fn int-valued? [s]
                      (cond (integer? s) true
                            (ps/binding? s) (= :int (first (lookup s)))
                            (seq? s) (and (#{'+ '* '-} (first s))
                                          (every? int-valued? (rest s)))
                            :else false))
        int-term (fn int-term [s]
                   (cond (integer? s) (int-pattern s)
                         (ps/binding? s) (var-sym s)
                         :else
                         (let [[op & args] s
                               args (map int-term args)]
                           (case [op (count args)]
                             [+ 2] (cons 'Int.add args)
                             [* 2] (cons 'Int.mul args)
                             [- 1] (cons 'Int.neg args)
                             [- 2] (cons 'Int.sub args)
                             (unsupported! (str "unsupported skeleton " (pr-str s)) {:skeleton s})))))]
    (letfn [(go [s]
              (cond
                (int-valued? s) (list 'Emmy.PolyExpr.const (int-term s))
                (ps/binding? s) (var-sym s)
                (= 'x s) 'Emmy.PolyExpr.X
                (seq? s)
                (let [[op & args] s]
                  (case [op (count args)]
                    [+ 2] (list 'Emmy.PolyExpr.add (go (first args)) (go (second args)))
                    [* 2] (list 'Emmy.PolyExpr.mul (go (first args)) (go (second args)))
                    [- 1] (list 'Emmy.PolyExpr.neg (go (first args)))
                    [- 2] (list 'Emmy.PolyExpr.add (go (first args))
                                (list 'Emmy.PolyExpr.neg (go (second args))))
                    (unsupported! (str "unsupported skeleton " (pr-str s)) {:skeleton s})))
                :else (unsupported! (str "unsupported skeleton " (pr-str s)) {:skeleton s})))]
      (go s))))

(defn- pattern->term
  "The pattern as a term, with wildcards replaced by fresh variables (for the
  rule's soundness lemma). Returns `[term extra-vars]`."
  [pattern]
  (let [extra (atom [])
        term (walk/prewalk
              (fn [f] (cond (= '_ f) (let [v (gensym "w_")] (swap! extra conj [v :poly]) v)
                            (= '(Emmy.PolyExpr.X) f) 'Emmy.PolyExpr.X
                            :else f))
              pattern)]
    [term @extra]))

(defn- parse-rules [rules]
  (when-not (zero? (mod (count rules) 3))
    (unsupported! "rules must be triples: lhs => rhs" {:rules rules}))
  (vec (for [[lhs arrow rhs] (partition 3 rules)]
         (do (when-not (= '=> arrow)
               (unsupported! (str "expected => in rule " (pr-str [lhs arrow rhs])) {}))
             (let [vars (atom [])
                   pat (compile-pattern lhs vars)]
               {:lhs lhs :rhs rhs :pattern pat :vars @vars
                :skeleton (compile-skeleton rhs @vars)})))))

;; ## Installation

(def ^:private eval-rules (mapv first ax/eval-equations))

(defn- kname [set-name & parts]
  (symbol (apply str "Emmy.Rules." set-name parts)))

(defn- binder [[v kind]]
  [v :- (if (= kind :int) 'Int 'Emmy.PolyExpr)])

(defn- eval-at [term]
  (list 'Emmy.PolyExpr.eval 'x 'rho term))

(defn- prove-rule! [set-name i {:keys [lhs rhs pattern skeleton vars]}]
  (let [nm (kname set-name ".rule_" i)
        [term extra] (pattern->term pattern)]
    (when-not (k/installed? nm)
      (try
        (k/quietly
         (a/prove-theorem nm
                          (vec (concat (mapcat binder (concat vars extra))
                                       '[x :- Int rho :- (=> Nat Int)]))
                          (list '= 'Int (eval-at term) (eval-at skeleton))
                          [(list 'int_ring eval-rules)]))
        (catch Throwable t
          (throw (ex-info (str "ruleset " set-name ": rule " i " is not sound: "
                               (pr-str lhs) " => " (pr-str rhs))
                          {:type ::unsound :rule i :lhs lhs :rhs rhs}
                          t)))))))

(defn- simp-body [simp step]
  (list 'match 'e
        ['(Emmy.PolyExpr.const c) (list step '(Emmy.PolyExpr.const c))]
        ['(Emmy.PolyExpr.X) (list step 'Emmy.PolyExpr.X)]
        ['(Emmy.PolyExpr.add a b) (list step (list 'Emmy.PolyExpr.add (list simp 'a) (list simp 'b)))]
        ['(Emmy.PolyExpr.mul a b) (list step (list 'Emmy.PolyExpr.mul (list simp 'a) (list simp 'b)))]
        ['(Emmy.PolyExpr.neg a) (list step (list 'Emmy.PolyExpr.neg (list simp 'a)))]
        ['(Emmy.PolyExpr.param j) (list step '(Emmy.PolyExpr.param j))]))

(defn- simp-equations [simp step]
  (let [P 'Emmy.PolyExpr, app (fn [& xs] (apply list xs))]
    [[(symbol (str simp "_const")) '[c :- Int]
      (app '= P (app simp '(Emmy.PolyExpr.const c)) (app step '(Emmy.PolyExpr.const c)))]
     [(symbol (str simp "_X")) []
      (app '= P (app simp 'Emmy.PolyExpr.X) (app step 'Emmy.PolyExpr.X))]
     [(symbol (str simp "_add")) '[a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
      (app '= P (app simp '(Emmy.PolyExpr.add a b))
           (app step (app 'Emmy.PolyExpr.add (app simp 'a) (app simp 'b))))]
     [(symbol (str simp "_mul")) '[a :- Emmy.PolyExpr b :- Emmy.PolyExpr]
      (app '= P (app simp '(Emmy.PolyExpr.mul a b))
           (app step (app 'Emmy.PolyExpr.mul (app simp 'a) (app simp 'b))))]
     [(symbol (str simp "_neg")) '[a :- Emmy.PolyExpr]
      (app '= P (app simp '(Emmy.PolyExpr.neg a))
           (app step (app 'Emmy.PolyExpr.neg (app simp 'a))))]
     [(symbol (str simp "_param")) '[j :- Nat]
      (app '= P (app simp '(Emmy.PolyExpr.param j)) (app step '(Emmy.PolyExpr.param j)))]]))

(defonce ^:private installed-rules (atom {}))

(defn ruleset*
  "Compiles the rule set `set-name` (a symbol) from `rules`, a flat sequence
  of `lhs => rhs` triples, into verified Ansatz definitions (see the namespace
  docstring). Returns a map describing it. Idempotent for identical rules;
  redefining a name with different rules throws."
  [set-name rules]
  (let [set-name (str set-name)
        rules (vec rules)]
    (when-let [old (get @installed-rules set-name)]
      (when (not= old rules)
        (throw (ex-info (str "ruleset " set-name " is already defined with different rules")
                        {:type ::redefined :name set-name}))))
    (ax/install!)
    (alg/install!)
    (let [parsed (parse-rules rules)
          step (kname set-name ".step")
          simp (kname set-name ".simp")
          step-thm (kname set-name ".step_correct")
          simp-thm (kname set-name ".simp_correct")
          simp-eqs (simp-equations simp step)]
      (locking k/install-lock
        (doseq [[i rule] (map-indexed vector parsed)]
          (prove-rule! set-name i rule))
        (ax/define! step '[e :- Emmy.PolyExpr] 'Emmy.PolyExpr
                    (apply list 'match 'e
                           (concat (map (juxt :pattern :skeleton) parsed)
                                   [['_ 'e]])))
        (when-not (k/installed? step-thm)
          (k/quietly
           (a/prove-theorem step-thm '[e :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
                            (list '= 'Int (eval-at (list step 'e)) (eval-at 'e))
                            [(list 'int_ring_split (into [step] eval-rules))])))
        (ax/define! simp '[e :- Emmy.PolyExpr] 'Emmy.PolyExpr
                    (simp-body simp step))
        (ax/prove-equations! simp-eqs)
        (when-not (k/installed? simp-thm)
          (let [rs (vec (concat (map first simp-eqs) [step-thm] eval-rules))
                case (fn [& ihs] (list 'int_ring (into rs ihs)))]
            (k/quietly
             (a/prove-theorem simp-thm '[e :- Emmy.PolyExpr x :- Int rho :- (=> Nat Int)]
                              (list '= 'Int (eval-at (list simp 'e)) (eval-at 'e))
                              ['(induction e) (case) (case)
                               (case 'ih_a 'ih_b) (case 'ih_a 'ih_b) (case 'ih_a) (case)])))))
      (swap! installed-rules assoc set-name rules)
      {:name set-name
       :rules rules
       :step (str step)
       :simp (str simp)
       :theorems (mapv str (concat (for [i (range (count parsed))] (kname set-name ".rule_" i))
                                   [step-thm simp-thm]))})))

(defmacro defruleset
  "Defines `name` as a verified rule set (see [[ruleset*]]):

  ```clojure
  (defruleset units
    (+ 0 ?a) => ?a
    (* 1 ?a) => ?a)
  ```"
  [name & rules]
  `(def ~name (ruleset* '~name '~rules)))

;; ## Running rule sets

(defn rewrite
  "Applies `ruleset`'s verified `simp` to the runtime `PolyExpr` `value`
  until it stops changing (at most `max-iterations`, default 100)."
  ([ruleset value] (rewrite ruleset value 100))
  ([ruleset value max-iterations]
   (let [simp (ax/compiled-fn (:simp ruleset))]
     (loop [v value, n max-iterations]
       (let [v' (simp v)]
         (if (or (= v v') (zero? n)) v' (recur v' (dec n))))))))

(defn simplifier
  "Returns a function that rewrites an Emmy polynomial expression with
  `ruleset`, like Emmy's `rule-simplifier`, and returns the result as an Emmy
  expression. `var` (default `'x`) is the variable the rules' `x` stands for;
  other symbols are parameters, which patterns match only through `?a` or `_`."
  ([ruleset] (simplifier ruleset 'x))
  ([ruleset var]
   (fn [expr]
     (let [ir (ax/->ir expr)
           params (ax/params-of ir var)]
       (-> (ax/ir->value ir var params)
           (->> (rewrite ruleset))
           (codegen/->emmy var params))))))
