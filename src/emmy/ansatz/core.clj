#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.core
  "Shared foundation of the Emmy ⇄ Ansatz bridge: kernel environment lifecycle
  and direct construction of kernel terms and proofs over `Int`.

  [Ansatz](https://github.com/replikativ/ansatz) is a Lean-4-compatible kernel
  for Clojure. In this bridge, Ansatz is the source of truth: the expression
  AST and the operations on it (so far, differentiation) are defined and
  proved correct inside Ansatz (see [[emmy.ansatz.expression]],
  [[emmy.ansatz.calculus]]), run natively through Ansatz's code generator, and
  only then handed to Emmy (see [[emmy.ansatz.codegen]]) for simplification,
  rendering, TeX, etc.

  Terms here are built directly instead of through Ansatz's surface elaborator.
  At Ansatz 0.2.84 the elaborator types `(- 0 3)` and `(- x)` as `Nat.sub`, and
  its `ring`, `omega` and `grind` tactics can't close symbolic `Int`
  identities. [[emmy.ansatz.algebra]] fills that gap with a proof-producing
  normalizer built on these builders.

  Terms are spelled exactly as Lean's `Init` states its `Int` lemmas, e.g.
  `@HAdd.hAdd Int Int Int (instHAdd Int Int.instAdd) a b`, so instantiating a
  lemma and chaining it with `Eq.trans` needs only syntactic matching. The
  kernel still checks every step up to definitional equality.

  Equality proofs are represented as maps `{:lhs a, :rhs b, :term p}` where
  `p : a = b`. Carrying both sides around is what lets [[trans]], [[symm]] and
  the congruence builders fill in the implicit arguments of `Eq.trans`,
  `congr`, etc."
  (:require [ansatz.codegen :as acg]
            [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as lvl]
            [ansatz.kernel.name :as name]))

;; ## Environment

(defn- int-ctor-lowering
  "Codegen for an `Int` constructor, applied or as a function value. `op` maps
  the compiled `Nat` field to the runtime integer."
  [op]
  (fn [env expr names]
    (let [[_ args] (e/get-app-fn-args expr)]
      (if (seq args)
        (op (acg/ansatz->clj env (first args) names))
        (let [n (gensym "n_")]
          (list 'clojure.core/fn [n] (op n)))))))

(defn- lower-int-rec
  "Codegen for `@Int.rec motive ofNat negSucc t extra…`."
  [env expr names]
  (let [[_ args] (e/get-app-fn-args expr)
        emit #(acg/ansatz->clj env % names)]
    (when (< (count args) 4)
      (throw (ex-info "Int.rec without its major premise is not supported" {})))
    (let [[_ on-nat on-neg major & extra] args
          t (gensym "int_")
          body (list 'clojure.core/let [t (emit major)]
                     (list 'if (list 'clojure.core/neg? t)
                           (list (emit on-neg) (list 'clojure.core/-' -1 t))
                           (list (emit on-nat) t)))]
      (reduce (fn [f arg] (list f (emit arg))) body extra))))

(def ^:private int-lowerings
  ;; Ansatz represents `Int` at runtime as a Clojure integer, but lowers
  ;; neither its constructors (they'd become tagged vectors) nor its recursor
  ;; (its generic recursor lowering covers `Nat`, `List`, enums and tagged
  ;; vectors). `Int.ofNat n` is `n` and `Int.negSucc n` is `-(n + 1)`, so the
  ;; recursor dispatches on the sign; `Int` isn't recursive, so no induction
  ;; hypotheses are involved.
  {"Int.ofNat"   (int-ctor-lowering identity)
   "Int.negSucc" (int-ctor-lowering (fn [n] (list 'clojure.core/-' -1 n)))
   "Int.rec"     lower-int-rec})

(defn ensure-init!
  "Loads Ansatz's bundled `Init` tier (≈3.6k Lean declarations, trust mode)
  into the global Ansatz environment, unless an environment is already loaded
  (e.g. a Mathlib store via `ansatz.core/init!`), and registers runtime
  lowerings for `Int`'s constructors and recursor. Returns the environment."
  []
  (locking a/ansatz-env
    (when-not @a/ansatz-env
      ;; `a/init!` prints a banner unconditionally; keep library loads quiet.
      (with-out-str
        (binding [a/*verbose* false]
          (a/init!))))
    (when-not (contains? @a/codegen-registry "Int.rec")
      (swap! a/codegen-registry merge int-lowerings)))
  (a/env))

(defonce ^{:doc "Serializes installation of definitions into the global Ansatz environment."}
  install-lock
  (Object.))

(defn env
  "The current global Ansatz kernel environment, initializing it if needed."
  []
  (ensure-init!))

(defmacro quietly
  "Evaluates `body` with Ansatz's progress output suppressed."
  [& body]
  `(binding [a/*verbose* false] ~@body))

(defn installed?
  "True if the kernel environment has a constant named `s`."
  [s]
  (a/has-constant? (str s)))

;; ## Constants

(def ^:private l0 lvl/zero)
(def ^:private l1 (lvl/succ lvl/zero))

(defn const
  "Kernel constant named by the dotted string `s`, at universe `levels`."
  [s & levels]
  (e/const' (name/from-string s) (vec levels)))

(def int-type
  "The kernel type `Int`."
  (const "Int"))

(def ^:private int->int (e/arrow int-type int-type))

(def ^:private add-op
  (e/app* (const "HAdd.hAdd" l0 l0 l0) int-type int-type int-type
          (e/app* (const "instHAdd" l0) int-type (const "Int.instAdd"))))

(def ^:private mul-op
  (e/app* (const "HMul.hMul" l0 l0 l0) int-type int-type int-type
          (e/app* (const "instHMul" l0) int-type (const "Int.instMul"))))

(def ^:private sub-op
  (e/app* (const "HSub.hSub" l0 l0 l0) int-type int-type int-type
          (e/app* (const "instHSub" l0) int-type (const "Int.instSub"))))

(def ^:private neg-op
  (e/app* (const "Neg.neg" l0) int-type (const "Int.instNegInt")))

;; ## Terms

(defn add "`a + b` in `Int`." [a b] (e/app* add-op a b))
(defn mul "`a * b` in `Int`." [a b] (e/app* mul-op a b))
(defn sub "`a - b` in `Int`." [a b] (e/app* sub-op a b))
(defn neg "`-a` in `Int`." [a] (e/app neg-op a))

(defn- nat-lit [n]
  (e/app* (const "OfNat.ofNat" l0) int-type (e/lit-nat n)
          (e/app (const "instOfNat") (e/lit-nat n))))

(defn lit
  "Integer literal. Negative literals are `-(n)`, which is how `Init` spells
  them, e.g. the `-1` in `Int.neg_eq_neg_one_mul`."
  [n]
  {:pre [(integer? n)]}
  (let [n (biginteger n)]
    (if (neg? (.signum n))
      (neg (nat-lit (.negate n)))
      (nat-lit n))))

(def zero (lit 0))
(def one (lit 1))

(defn eq
  "The proposition `a = b` in `Int`."
  [a b]
  (e/app* (const "Eq" l1) int-type a b))

(defn eq-at
  "The proposition `a = b` at `type`, which lives in `Sort level`."
  [type level a b]
  (e/app* (const "Eq" level) type a b))

(defn eq-view
  "For a kernel proposition `@Eq.{u} T lhs rhs`, returns
  `{:type T :level u :lhs lhs :rhs rhs}`; nil for anything else."
  [prop]
  (let [[head args] (e/get-app-fn-args prop)]
    (when (and (e/const? head)
               (= "Eq" (name/->string (e/const-name head)))
               (= 3 (count args)))
      {:type  (nth args 0)
       :level (first (e/const-levels head))
       :lhs   (nth args 1)
       :rhs   (nth args 2)})))

;; ## Proofs
;;
;; `:type` and `:level` default to `Int` and universe 1; proofs about other
;; types (e.g. an AST) carry them explicitly.

(defn refl
  "Proof of `a = a`, at type `Int` unless `type` (living in `Sort level`) is
  given."
  ([a] (refl a int-type l1))
  ([a type level]
   {:lhs a :rhs a :type type :level level
    :term (e/app* (const "Eq.refl" level) type a)}))

(defn refl?
  "True if `p` is a reflexivity proof, which lets builders skip no-op steps."
  [p]
  (identical? (:lhs p) (:rhs p)))

(defn- type+level [p]
  [(:type p int-type) (:level p l1)])

(defn symm
  "From `p : a = b`, proof of `b = a`."
  [{:keys [lhs rhs term] :as p}]
  (if (refl? p)
    p
    (let [[t u] (type+level p)]
      {:lhs rhs :rhs lhs :type t :level u
       :term (e/app* (const "Eq.symm" u) t lhs rhs term)})))

(defn trans
  "From `p : a = b` and `q : b = c`, proof of `a = c`. `b` must be the same
  term on both sides (checked up to definitional equality by the kernel)."
  ([p] p)
  ([p q]
   (cond (refl? p) q
         (refl? q) p
         :else (let [[t u] (type+level p)]
                 {:lhs (:lhs p) :rhs (:rhs q) :type t :level u
                  :term (e/app* (const "Eq.trans" u) t
                                (:lhs p) (:rhs p) (:rhs q)
                                (:term p) (:term q))})))
  ([p q & more]
   (reduce trans (trans p q) more)))

(defn congr-app
  "Congruence through one application. From `pf : f = f'` (or nil, meaning
  `f` is unchanged) and `pa : a = a'`, proof of `f a = f' a'`. `f` must have
  the non-dependent type `dom → cod`, with `dom : Sort u` and `cod : Sort v`."
  [f pf pa {:keys [dom cod u v]}]
  (let [f' (if pf (:rhs pf) f)]
    (cond
      (and (nil? pf) (refl? pa))
      (refl (e/app f (:lhs pa)) cod v)

      (nil? pf)
      {:lhs (e/app f (:lhs pa)) :rhs (e/app f (:rhs pa)) :type cod :level v
       :term (e/app* (const "congrArg" u v) dom cod (:lhs pa) (:rhs pa) f (:term pa))}

      :else
      {:lhs (e/app f (:lhs pa)) :rhs (e/app f' (:rhs pa)) :type cod :level v
       :term (e/app* (const "congr" u v) dom cod f f' (:lhs pa) (:rhs pa)
                     (:term pf) (:term pa))})))

(defn- congr-binop
  "From `p : a = a'` and `q : b = b'`, proof of `op a b = op a' b'`."
  [op p q]
  (if (and (refl? p) (refl? q))
    (refl (e/app* op (:lhs p) (:lhs q)))
    (let [fp (e/app* (const "congrArg" l1 l1) int-type int->int
                     (:lhs p) (:rhs p) op (:term p))]
      {:lhs  (e/app* op (:lhs p) (:lhs q))
       :rhs  (e/app* op (:rhs p) (:rhs q))
       :term (e/app* (const "congr" l1 l1) int-type int-type
                     (e/app op (:lhs p)) (e/app op (:rhs p))
                     (:lhs q) (:rhs q)
                     fp (:term q))})))

(defn congr-add
  "From `p : a = a'` and `q : b = b'`, proof of `a + b = a' + b'`."
  [p q]
  (congr-binop add-op p q))

(defn congr-mul
  "From `p : a = a'` and `q : b = b'`, proof of `a * b = a' * b'`."
  [p q]
  (congr-binop mul-op p q))

(defn lemma
  "Instantiates the `Init` equation named `lemma-name` (e.g. `\"Int.add_mul\"`)
  at the explicit arguments `args`, returning a proof map. The lemma's
  statement comes from the kernel environment, so the sides are exactly what
  the kernel expects."
  [lemma-name & args]
  (let [ci (or (env/lookup (env) (name/from-string lemma-name))
               (throw (ex-info (str "Unknown lemma " lemma-name) {:lemma lemma-name})))
        prop (reduce (fn [t a]
                       (when-not (e/forall? t)
                         (throw (ex-info (str "Too many arguments for " lemma-name)
                                         {:lemma lemma-name})))
                       (e/instantiate1 (e/forall-body t) a))
                     (env/ci-type ci)
                     args)
        view (or (eq-view prop)
                 (throw (ex-info (str lemma-name " is not an equation")
                                 {:lemma lemma-name :prop (e/->string prop)})))]
    (assoc view
           :term (apply e/app* (const lemma-name) args))))

;; ## Closed statements

(def ^:private fvar-counter
  ;; Ids far away from anything the Ansatz elaborator hands out. They never
  ;; reach the kernel: [[close]] abstracts them away first.
  (atom 7000000000))

(defn fresh-vars
  "Returns `[sym fvar]` pairs, a fresh `Int` free variable per symbol, in
  order. Use with [[close]]."
  [syms]
  (mapv (fn [s] [s (e/fvar (swap! fvar-counter inc))]) syms))

(defn close
  "Binds the free variables `vars` (a seq of `[sym fvar]`, outermost first).
  Returns `{:statement (∀ vars, lhs = rhs), :proof (λ vars, term)}` for the
  proof map `p`."
  [vars p]
  (let [ids   (mapv (comp e/fvar-id second) vars)
        names (mapv (comp str first) vars)
        wrap  (fn [binder body]
                (reduce (fn [acc nm] (binder nm int-type acc :default))
                        (e/abstract-many body ids)
                        (rseq names)))]
    {:statement (wrap e/forall' (eq (:lhs p) (:rhs p)))
     :proof     (wrap e/lam (:term p))}))

(defn ->string
  "Human-readable rendering of a kernel term."
  [expr]
  (e/->string expr))
