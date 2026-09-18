#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.match
  "A pattern-matching front end for Ansatz definitions.

  Ansatz 0.2.84 elaborates a `match` correctly when every pattern is one level
  deep (`(C x y)`, `_`, a variable, or a `Nat` literal) and the match is the
  whole function body. Two shapes fail:

  - nested sub-patterns mixed with variables on the same constructor, e.g.
    `[(Int.ofNat 0) a] [(Int.ofNat n) b]` (the second arm loses `n`), and
  - a `match` below the top, e.g. on a variable bound by an outer pattern
    (a free variable leaks into the kernel term).

  [[desugar]] rewrites a definition into shapes Ansatz does handle:

  1. **Flattening.** A `match` with nested sub-patterns becomes a decision
     tree of one-level matches, column by column (the classic algorithm for
     compiling pattern matrices). Arms keep their order, so the first matching
     arm wins as before. Number literals in sub-positions become
     `Nat.zero`/`Nat.succ` patterns.

  2. **Lambda lifting.** Every `match` below the top of a body becomes an
     auxiliary definition `<name>._match_<k>` whose parameters are the
     variables it uses, typed from the enclosing parameters and constructor
     signatures; the `match` is replaced by a call.

  The output is ordinary Ansatz surface syntax, elaborated and checked by the
  kernel like anything else, so this namespace is not trusted: a mistake here
  yields a definition that fails to check or, for a well-typed but different
  function, a correctness theorem that fails to prove.

  Limitations: constructors of parameterized inductives (e.g. `List α`) are
  not supported in flattened or lifted positions, and a lifted `match` may not
  call the function being defined (that would hide structural recursion)."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.name :as name]
            [emmy.ansatz.core :as k]))

(defn- unsupported! [msg data]
  (throw (ex-info (str "match: " msg) (assoc data :type ::unsupported))))

;; ## Constructors

(defn- expr->form
  "Surface form of a closed, non-dependent kernel type such as `Int` or
  `Emmy.PolyExpr`."
  [expr]
  (cond
    (e/const? expr) (symbol (name/->string (e/const-name expr)))
    (e/app? expr) (let [[head args] (e/get-app-fn-args expr)]
                    (apply list (map expr->form (cons head args))))
    :else (unsupported! (str "can't express type " (k/->string expr)) {})))

(defn- ctor-info
  "`{:name sym :induct str :field-types [form…]}` if `sym` names a
  constructor, else nil."
  [sym]
  (when (symbol? sym)
    (when-let [ci (env/lookup (k/env) (name/from-string (str sym)))]
      (when (.isCtor ^ansatz.kernel.ConstantInfo ci)
        (when (pos? (.numParams ^ansatz.kernel.ConstantInfo ci))
          (unsupported! (str "constructor of a parameterized type: " sym) {:ctor sym}))
        (let [nf (.numFields ^ansatz.kernel.ConstantInfo ci)
              types (loop [t (env/ci-type ci), acc []]
                      (if (and (e/forall? t) (< (count acc) nf))
                        (let [ft (e/forall-type t)]
                          (when (e/has-loose-bvars? ft)
                            (unsupported! (str "dependent constructor field in " sym) {:ctor sym}))
                          (recur (e/forall-body t) (conj acc (expr->form ft))))
                        acc))
              induct (let [s (str sym)] (subs s 0 (.lastIndexOf s ".")))]
          {:name sym :induct induct :field-types types})))))

(defn- ctors-of
  "Constructor symbols of the inductive named `induct`, in declaration order."
  [induct]
  (let [ci (env/lookup (k/env) (name/from-string induct))]
    (mapv #(symbol (name/->string %)) (.ctors ^ansatz.kernel.ConstantInfo ci))))

;; ## Patterns
;;
;; Normalized patterns: {:wild true}, {:var sym} or {:ctor sym :args [pat…]}.

(defn- normalize [p]
  (cond
    (= '_ p) {:wild true}
    (and (integer? p) (not (neg? p)))
    (if (zero? p)
      {:ctor 'Nat.zero :args []}
      {:ctor 'Nat.succ :args [(normalize (dec p))]})
    (symbol? p) (if (ctor-info p) {:ctor p :args []} {:var p})
    (and (seq? p) (ctor-info (first p)))
    {:ctor (first p) :args (mapv normalize (rest p))}
    :else (unsupported! (str "unsupported pattern " (pr-str p)) {:pattern p})))

(defn- irrefutable? [p]
  (or (:wild p) (:var p)))

(defn- nested?
  "True if some arm's pattern has a non-variable sub-pattern."
  [arms]
  (some (fn [[pat _]]
          (and (seq? pat)
               (some #(or (seq? %) (number? %)
                          (and (symbol? %) (not= '_ %) (ctor-info %)))
                     (rest pat))))
        arms))

(defn- bind
  "Wraps `rhs` in `let` bindings for pattern variables bound to scrutinees."
  [rhs bindings]
  (let [bindings (remove (fn [[v s]] (= v s)) bindings)]
    (if (seq bindings)
      (list 'let (vec (mapcat identity bindings)) rhs)
      rhs)))

(defn- compile-rows
  "Compiles the pattern matrix `rows` (`{:pats [pat…] :rhs form :binds
  [[var scrutinee]…]}`) over the scrutinee symbols `scruts` into nested
  one-level matches."
  [scruts rows]
  (when (empty? rows)
    (unsupported! "non-exhaustive match" {:scrutinees scruts}))
  (let [{:keys [pats rhs binds]} (first rows)
        j (first (keep-indexed (fn [i p] (when-not (irrefutable? p) i)) pats))]
    (if (nil? j)
      (bind rhs (concat binds (keep-indexed (fn [i p] (when-let [v (:var p)] [v (scruts i)]))
                                            pats)))
      (let [ctors (ctors-of (:induct (ctor-info (:ctor (pats j)))))
            sj (scruts j)
            arms
            (for [c ctors
                  :let [nf (count (:field-types (ctor-info c)))
                        fields (vec (repeatedly nf #(gensym "m_")))
                        scruts' (vec (concat (subvec scruts 0 j) fields (subvec scruts (inc j))))
                        rows' (keep (fn [{:keys [pats] :as row}]
                                      (let [p (pats j)
                                            splice #(vec (concat (subvec pats 0 j) % (subvec pats (inc j))))]
                                        (cond
                                          (:ctor p) (when (= c (:ctor p))
                                                      (assoc row :pats (splice (:args p))))
                                          :else (cond-> (assoc row :pats (splice (repeat nf {:wild true})))
                                                  (:var p) (update :binds conj [(:var p) sj])))))
                                    rows)]]
              [(apply list c fields) (compile-rows scruts' (vec rows'))])]
        (apply list 'match sj (map vec arms))))))

(defn- flatten-match
  "Flattens `(match d arms…)` if any arm has nested sub-patterns."
  [[_ d & arms :as form]]
  (if-not (nested? arms)
    form
    (do (when-not (symbol? d)
          (unsupported! "a match with nested patterns must be on a variable" {:form form}))
        (compile-rows [d] (mapv (fn [[pat rhs]] {:pats [(normalize pat)] :rhs rhs :binds []})
                                arms)))))

;; ## Lambda lifting

(defn- match-form? [form]
  (and (seq? form) (= 'match (first form))))

(defn- symbols-in [form]
  (set (filter symbol? (tree-seq coll? seq form))))

(defn- arm-scope
  "Scope entries for the variables bound by `pattern` on scrutinee `d`."
  [scope d pattern]
  (cond
    (and (seq? pattern) (ctor-info (first pattern)))
    (map vector (rest pattern) (:field-types (ctor-info (first pattern))))

    (and (symbol? pattern) (not= '_ pattern) (not (ctor-info pattern)))
    [[pattern (get (into {} scope) d)]]

    :else []))

(declare lift)

(defn- lift-body
  "Walks `form`, lifting each `match` below the top into an auxiliary
  definition (recorded in the `defs` atom). `scope` is a vector of
  `[sym type-form]`, latest binding last; `tail-type` is the type of `form`
  when it is in tail position, else nil."
  [ctx scope form tail-type top?]
  (cond
    (match-form? form)
    (if top?
      (let [[_ d & arms] (flatten-match form)]
        (apply list 'match d
               (for [[pat rhs] arms]
                 [pat (lift-body ctx (into scope (arm-scope scope d pat)) rhs tail-type false)])))
      (lift ctx scope form tail-type))

    (and (seq? form) (= 'let (first form)))
    (let [[_ bindings body] form
          scope' (into scope (map (fn [[v init]] [v (get (into {} scope) init)])
                                  (partition 2 bindings)))]
      (list 'let bindings (lift-body ctx scope' body tail-type false)))

    (seq? form)
    (apply list (map #(lift-body ctx scope % nil false) form))

    :else form))

(defn- lift
  "Lifts the non-top-level `match` `form` into an auxiliary definition and
  returns the call that replaces it."
  [{:keys [fname defs] :as ctx} scope form tail-type]
  (let [used (symbols-in form)
        _ (when (contains? used fname)
            (unsupported! (str "a nested match may not call " fname) {:form form}))
        free (->> (reverse scope)
                  (reduce (fn [[seen acc] [v t]]
                            (if (or (seen v) (not (used v)))
                              [seen acc]
                              [(conj seen v) (conj acc [v t])]))
                          [#{} []])
                  second
                  reverse)
        _ (doseq [[v t] free]
            (when (nil? t)
              (unsupported! (str "can't determine the type of " v) {:var v})))
        aux (symbol (str fname "._match_" (count @defs)))
        params (vec (mapcat (fn [[v t]] [v :- t]) free))
        _ (swap! defs conj nil)                      ; reserve the index
        slot (dec (count @defs))
        body (lift-body ctx (vec free) form tail-type true)]
    (swap! defs assoc slot [aux params (or tail-type '_) body])
    (if (seq free)
      (apply list aux (map first free))
      aux)))

(defn desugar
  "Rewrites the Ansatz definition `[name params ret body]` into a sequence of
  definitions in dependency order, the last being `name` itself (see the
  namespace docstring). Definitions that need no rewriting come back
  unchanged."
  [fname params ret body]
  (let [defs  (atom [])
        scope (vec (for [[v _ t] (partition 3 params)] [v t]))
        body' (lift-body {:fname fname :defs defs} scope body ret true)]
    (conj (vec (reverse @defs)) [fname params ret body'])))
