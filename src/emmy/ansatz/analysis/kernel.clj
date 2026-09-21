#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.kernel
  "Typed term builders for the independent analysis library.
  Every new definition and theorem passes through check-constant. No axiom
  constructor or unchecked environment insertion is exposed here."
  (:require [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [emmy.ansatz.core :as k]))

;; ## Core term constructors

(def type0
  "The first universe (`Type`)."
  (e/sort' (level/succ level/zero)))

(def prop
  "The universe of propositions."
  (e/sort' level/zero))

(defonce ^:private ids (atom 8000000000))

(defn pi
  "Build a dependent function type, abstracting over a fresh free variable."
  [label domain body]
  (let [id (swap! ids inc)]
    (e/forall' label domain (e/abstract1 (body (e/fvar id)) id) :default)))

(defn lam
  "Build a typed lambda term, abstracting over a fresh free variable."
  [label domain body]
  (let [id (swap! ids inc)]
    (e/lam label domain (e/abstract1 (body (e/fvar id)) id) :default)))

(defmacro forall
  "Constructs nested dependent function types from [symbol type] bindings."
  [bindings body]
  (reduce (fn [body [sym domain]]
            `(pi ~(str sym) ~domain (fn [~sym] ~body)))
          body (reverse bindings)))

(defmacro lambda
  "Constructs nested typed lambda terms from [symbol type] bindings."
  [bindings body]
  (reduce (fn [body [sym domain]]
            `(lam ~(str sym) ~domain (fn [~sym] ~body)))
          body (reverse bindings)))

(defmacro with-cont
  "Flattens continuation-last proof builders into sequential bindings.

  (with-cont [[w hw] (eliminate witness goal)
              [v hv] (eliminate (use w hw) goal)]
    (finish w hw v hv))

  Expands to nested calls with ordinary Clojure fn continuations. It introduces
  no kernel declarations, axioms or implicit proof steps. Branching eliminators
  remain explicit. Each binding vector names the continuation arguments."
  [bindings body]
  (when-not (and (vector? bindings) (even? (count bindings)))
    (throw (IllegalArgumentException. "with-cont expects an even binding vector")))
  (reduce
   (fn [tail [params call]]
     (when-not (and (vector? params) (every? symbol? params) (seq? call))
       (throw (IllegalArgumentException. "with-cont expects [symbols] and a call")))
     `(~@call (fn ~params ~tail)))
   body (reverse (partition 2 bindings))))

(defn arrow
  "Build an implication or non-dependent function type `a → b`."
  [a b]
  (e/arrow a b))

(defmacro >->
  "Constructs a right-associative implication chain.

  `(>-> A B C)` expands to `(arrow A (arrow B C))`; the final form is
  the conclusion and every preceding form is a premise."
  [& forms]
  (when (< (count forms) 2)
    (throw (IllegalArgumentException.
            ">-> expects at least a premise and a conclusion")))
  (reduce (fn [conclusion premise]
            `(arrow ~premise ~conclusion))
          (last forms)
          (reverse (butlast forms))))

(defn app
  "Apply a kernel function to one or more arguments."
  [f & xs]
  (apply e/app* f xs))

(defn predicate
  "Build the predicate type `a → Prop`."
  [a]
  (arrow a prop))

(defn and' [a b]
  (app (k/const "And") a b))

(defn exists' [a p]
  (app (k/const "Exists" (level/succ level/zero)) a p))

;; ## Checked declarations

(defn declare-constant
  "Pure. Checks a closed definition or theorem against the context's
  environment and returns the context extended with it. The kernel rejects a
  name that is already declared, so existing declarations are never silently
  trusted. `value` is a term, or a function of the context that returns one
  (for proofs that must see the declarations made so far)."
  [{:keys [env] :as ctx} kind label type value]
  (when-not (#{:def :thm} kind)
    (throw (ex-info "Only checked definitions and theorems are permitted" {:kind kind})))
  (let [value (if (fn? value) (value ctx) value)]
    (when (or (nil? type) (nil? value))
      (throw (ex-info "A declaration requires both a type and a value" {:name label})))
    (let [make (case kind :def env/mk-def :thm env/mk-thm)]
      (assoc ctx :env (env/check-constant env (make (name/from-string label) [] type value))))))

(defn declarer
  "A function `(decl ctx kind label type value)` that declares `prefix`+`label`
  and is idempotent: a constant already in the context is left alone, which is
  what lets every namespace's `install` be re-run against a context that has
  it. One of these replaces the per-namespace guard-and-install wrappers."
  [prefix]
  (fn [ctx kind label type value]
    (let [full (str prefix label)]
      (if (k/installed? ctx full)
        ctx
        (declare-constant ctx kind full type value)))))

(defn with-kind
  "Fixes the kind of a [[declarer]]: `(with-kind decl :thm)` is a function
  `(theorem ctx label type value)`."
  [decl kind]
  (fn [ctx label type value] (decl ctx kind label type value)))

(defn declaration
  "The installed declaration `label` with its complete type and value, or nil.
  The one-argument form reads the global environment (deprecated)."
  ([label] (declaration (k/base-ctx) label))
  ([ctx label]
   (when-let [ci (k/lookup ctx label)]
     {:kind (env/ci-tag ci) :statement (env/ci-type ci) :proof (env/ci-value ci)})))

(defn install-declaration!
  "Deprecated IO edge: declares one constant in the global environment.
  Use [[declare-constant]] inside a context-threaded `install` instead."
  [kind label type value]
  (k/commit! #(declare-constant % kind label type value))
  (k/const label))

;; ## Logic
;;
;; Builders for proof terms in propositional and first-order logic. Each takes
;; the propositions involved explicitly, since kernel terms carry no implicit
;; arguments.

(def ^:private u0 level/zero)
(def ^:private u1 (level/succ level/zero))

(defn or' [a b]
  (app (k/const "Or") a b))

(defn not' [a]
  (app (k/const "Not") a))

(defn iff [a b]
  (app (k/const "Iff") a b))

(def false-prop
  "The proposition `False`."
  (k/const "False"))

(defn and-intro "Proof of `a ∧ b`." [a b pa pb]
  (app (k/const "And.intro") a b pa pb))

(defn and-left "Proof of `a` from `h : a ∧ b`." [a b h]
  (app (k/const "And.left") a b h))

(defn and-right "Proof of `b` from `h : a ∧ b`." [a b h]
  (app (k/const "And.right") a b h))

(defn or-inl "Proof of `a ∨ b` from `a`." [a b pa]
  (app (k/const "Or.inl") a b pa))

(defn or-inr "Proof of `a ∨ b` from `b`." [a b pb]
  (app (k/const "Or.inr") a b pb))

(defn or-elim
  "Proof of `c` from `h : a ∨ b`, `left : a → c` and `right : b → c`."
  [a b c h left right]
  (app (k/const "Or.elim") a b c h left right))

(defn exists-intro
  "Proof of `∃ x : α, p x` from a witness `w` and `h : p w`. `α : Type`."
  [alpha p w h]
  (app (k/const "Exists.intro" u1) alpha p w h))

(defn exists-elim
  "Proof of `c : Prop` from `h : ∃ x : α, p x` and `f : ∀ x, p x → c`."
  [alpha p c h f]
  (app (k/const "Exists.casesOn" u1) alpha p (lam "_" (exists' alpha p) (fn [_] c)) h f))

(defn false-elim "Proof of `c : Prop` from `h : False`." [c h] (app (k/const "False.elim" u0) c h))

(defn absurd'
  "Proof of `c : Prop` from `h : a` and `n : ¬a`."
  [a c h n]
  (app (k/const "absurd" u0) a c h n))

(defn decidable-em
  "Proof of `p ∨ ¬p` from a `Decidable p` instance `inst`."
  [p inst]
  (app (k/const "Decidable.em") p inst))

(defn classical-em "Proof of `p ∨ ¬p` (uses `Classical.choice`)." [p]
  (app (k/const "Classical.em") p))

(defn cast-prop
  "Proof of `q` from `h : p` and `e : p = q` (propositions)."
  [p q e h]
  (app (k/const "Eq.mp" u0) p q e h))

(defn transport
  "Proof of `motive y` from `h : motive x`, given an `Int` equality proof map
  `p : x = y` (as built by `emmy.ansatz.core`). `motive` is a kernel lambda
  `Int → Prop`."
  [motive p h]
  (cast-prop (app motive (:lhs p)) (app motive (:rhs p))
             (app (k/const "congrArg" u1 u1) k/int-type prop (:lhs p) (:rhs p) motive (:term p))
             h))

(defn transport-at
  "Proof of `motive y` from `h : motive x` and `e : x = y`, where `x y : type`
  and `type : Sort level`; `motive` is a kernel lambda `type → Prop`."
  [type level motive x y e h]
  (cast-prop (app motive x) (app motive y)
             (app (k/const "congrArg" level u1) type prop x y motive e)
             h))

(defn propext' "Proof of `p = q` from `h : p ↔ q`." [p q h] (app (k/const "propext") p q h))

(defn iff-intro "Proof of `p ↔ q` from `mp : p → q` and `mpr : q → p`." [p q mp mpr]
  (app (k/const "Iff.intro") p q mp mpr))

;; ## Quotients (at universe 1: quotients of types)

(defn quot-type "The type `Quot r` for `r : α → α → Prop`, `α : Type`." [alpha r]
  (app (k/const "Quot" u1) alpha r))

(defn quot-mk "`Quot.mk r a`." [alpha r a] (app (k/const "Quot.mk" u1) alpha r a))

(defn quot-sound
  "Proof of `Quot.mk r a = Quot.mk r b` from `h : r a b`."
  [alpha r a b h]
  (app (k/const "Quot.sound" u1) alpha r a b h))

(defn quot-lift
  "`Quot.lift f resp : Quot r → β` for `f : α → β` (β : Type) and
  `resp : ∀ a b, r a b → f a = f b`."
  [alpha r beta f resp]
  (app (k/const "Quot.lift" u1 u1) alpha r beta f resp))

(defn quot-lift-prop
  "`Quot.lift f resp : Quot r → Prop` for a predicate `f : α → Prop` and
  `resp : ∀ a b, r a b → f a = f b`."
  [alpha r f resp]
  (app (k/const "Quot.lift" u1 u1) alpha r prop f resp))

(defn quot-ind
  "Proof of `∀ q : Quot r, motive q` from `h : ∀ a, motive (Quot.mk r a)`."
  [alpha r motive h]
  (app (k/const "Quot.ind" u1) alpha r motive h))

;; ## Axiom audit

(defn- constants-in
  "The names (strings) of the constants mentioned in `expr`."
  [expr]
  (loop [stack [expr] found #{}]
    (if (empty? stack)
      found
      (let [x (peek stack) stack (pop stack)]
        (case (e/tag x)
          :const (recur stack (conj found (name/->string (e/const-name x))))
          :app (recur (conj stack (e/app-fn x) (e/app-arg x)) found)
          :lam (recur (conj stack (e/lam-type x) (e/lam-body x)) found)
          :forall (recur (conj stack (e/forall-type x) (e/forall-body x)) found)
          :let (recur (conj stack (e/let-type x) (e/let-value x) (e/let-body x)) found)
          :mdata (recur (conj stack (e/mdata-expr x)) found)
          :proj (recur (conj stack (e/proj-struct x)) found)
          (recur stack found))))))

(defn axioms-of
  "The set of axioms (as name strings) that the declaration `label` depends on,
  transitively through the types and values of every constant it mentions.
  The one-argument form reads the global environment (deprecated)."
  ([label] (axioms-of (k/base-ctx) label))
  ([ctx label]
   (loop [todo [(str label)] seen #{} axioms #{}]
     (if-let [[s & more] (seq todo)]
       (if (seen s)
         (recur more seen axioms)
         (if-let [ci (k/lookup ctx s)]
           (recur (into more (mapcat constants-in)
                        (keep identity [(env/ci-type ci) (env/ci-value ci)]))
                  (conj seen s)
                  (cond-> axioms (env/axiom? ci) (conj s)))
           (recur more (conj seen s) axioms)))
       axioms))))

;; ## Generic quotient lifting
;;
;; `qc` describes a quotient of a type `:alpha : Type` by `:rel`, with
;; `:refl` (a ↦ proof of rel a a) and `:symm` ((a b h) ↦ proof of rel b a).
;; Operations and congruences are Clojure functions producing kernel terms.

(defn- quotient-terms
  "The term builders of a quotient description: its type `Quot r`, `Quot.mk`,
  `Quot.sound` and the relation applied to two elements."
  [{:keys [alpha rel]}]
  {:type (quot-type alpha rel)
   :mk (fn [a] (quot-mk alpha rel a))
   :sound (fn [a b h] (quot-sound alpha rel a b h))
   :related (fn [a b] (app rel a b))})

(defn lift1*
  "`Quot r → Quot r` lifting `op` (a ↦ term) with `congr` ((a b h) ↦ proof of
  `r (op a) (op b)`)."
  [{:keys [alpha rel] :as qc} op congr]
  (let [{:keys [mk sound related] Qt :type} (quotient-terms qc)]
    (lambda [[x Qt]]
      (app (quot-lift alpha rel Qt
                      (lambda [[a alpha]] (mk (op a)))
                      (lambda [[a alpha] [b alpha] [h (related a b)]]
                        (sound (op a) (op b) (congr a b h))))
           x))))

(defn quot-ind-all*
  "Proof of `P x₁ … xₙ` for the bound quotient variables `xs`, from `leaf`
  (representatives ↦ proof of `P (mk a₁) … (mk aₙ)`)."
  [{:keys [alpha rel] :as qc} xs motive leaf]
  (let [{:keys [mk] Qt :type} (quotient-terms qc)]
    (letfn [(go [done [x & more]]
              (if (nil? x)
                (leaf done)
                (app (quot-ind alpha rel
                               (lambda [[y Qt]] (apply motive (concat (map mk done) [y] more)))
                               (lambda [[a alpha]] (go (conj done a) more)))
                     x)))]
      (go [] (seq xs)))))

(defn lift2*
  "`Quot r → Quot r → Quot r` lifting the binary `op` with `congr`
  ((a a' b b' ha hb) ↦ proof of `r (op a b) (op a' b')`)."
  [{:keys [alpha rel refl] :as qc} op congr]
  (let [{:keys [mk sound related] Qt :type} (quotient-terms qc)
        ;; the map on the second argument, for a fixed first representative
        inner (fn [a y]
                (app (quot-lift alpha rel Qt
                                (lambda [[b alpha]] (mk (op a b)))
                                (lambda [[b alpha] [b' alpha] [h (related b b')]]
                                  (sound (op a b) (op a b') (congr a a b b' (refl a) h))))
                     y))]
    (lambda [[x Qt] [y Qt]]
      (app (quot-lift alpha rel Qt
                      (lambda [[a alpha]] (inner a y))
                      (lambda [[a alpha] [a' alpha] [h (related a a')]]
                        (app (quot-ind alpha rel
                                       (lambda [[z Qt]] (k/eq-at Qt u1 (inner a z) (inner a' z)))
                                       (lambda [[b alpha]]
                                         (sound (op a b) (op a' b) (congr a a' b b h (refl b)))))
                             y)))
           x))))
