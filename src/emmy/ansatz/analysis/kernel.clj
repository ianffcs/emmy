#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.kernel
  "Typed term builders for the independent analysis library.
  Every new definition and theorem passes through check-constant. No axiom
  constructor or unchecked environment insertion is exposed here."
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [ansatz.kernel.name :as name]
            [emmy.ansatz.core :as k]))

(def type0 (e/sort' (level/succ level/zero)))
(def prop (e/sort' level/zero))
(defonce ^:private ids (atom 8000000000))

(defn pi [label domain body]
  (let [id (swap! ids inc)]
    (e/forall' label domain (e/abstract1 (body (e/fvar id)) id) :default)))

(defn lam [label domain body]
  (let [id (swap! ids inc)]
    (e/lam label domain (e/abstract1 (body (e/fvar id)) id) :default)))

(defmacro forall
  "Constructs nested dependent function types from [symbol type] bindings."
  [bindings body]
  (reduce (fn [body [sym domain]] `(pi ~(str sym) ~domain (fn [~sym] ~body)))
          body (reverse bindings)))

(defmacro lambda
  "Constructs nested typed lambda terms from [symbol type] bindings."
  [bindings body]
  (reduce (fn [body [sym domain]] `(lam ~(str sym) ~domain (fn [~sym] ~body)))
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

(defn arrow [a b] (e/arrow a b))

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

(defn app [f & xs] (apply e/app* f xs))
(defn predicate [a] (arrow a prop))
(defn and' [a b] (app (k/const "And") a b))
(defn exists' [a p] (app (k/const "Exists" (level/succ level/zero)) a p))

(defn install-declaration!
  "Checks a closed definition or theorem and installs it atomically.
  Existing declarations are rejected rather than silently trusted."
  [kind label type value]
  (when-not (#{:def :thm} kind)
    (throw (ex-info "Only checked definitions and theorems are permitted" {:kind kind})))
  (when (or (nil? type) (nil? value))
    (throw (ex-info "A declaration requires both a type and a value" {:name label})))
  (k/ensure-init!)
  (locking k/install-lock
    (let [constructor (case kind :def env/mk-def :thm env/mk-thm)
          ci (constructor (name/from-string label) [] type value)]
      (swap! a/ansatz-env #(env/check-constant % ci))))
  (k/const label))

(defn declaration
  "Returns an installed declaration with its complete type and value."
  [label]
  (when-let [ci (env/lookup (k/env) (name/from-string label))]
    {:kind (env/ci-tag ci) :statement (env/ci-type ci) :proof (env/ci-value ci)}))

;; ## Logic
;;
;; Builders for proof terms in propositional and first-order logic. Each takes
;; the propositions involved explicitly, since kernel terms carry no implicit
;; arguments.

(def ^:private u0 level/zero)
(def ^:private u1 (level/succ level/zero))

(defn or' [a b] (app (k/const "Or") a b))
(defn not' [a] (app (k/const "Not") a))
(defn iff [a b] (app (k/const "Iff") a b))
(def false-prop "The proposition `False`." (k/const "False"))

(defn and-intro "Proof of `a ∧ b`." [a b pa pb] (app (k/const "And.intro") a b pa pb))
(defn and-left "Proof of `a` from `h : a ∧ b`." [a b h] (app (k/const "And.left") a b h))
(defn and-right "Proof of `b` from `h : a ∧ b`." [a b h] (app (k/const "And.right") a b h))
(defn or-inl "Proof of `a ∨ b` from `a`." [a b pa] (app (k/const "Or.inl") a b pa))
(defn or-inr "Proof of `a ∨ b` from `b`." [a b pb] (app (k/const "Or.inr") a b pb))

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

(defn axioms-of
  "The set of axioms (as name strings) that the declaration `label` depends on,
  transitively through the types and values of every constant it mentions."
  [label]
  (let [env (k/env)
        seen (java.util.HashSet.)
        axioms (atom #{})]
    (letfn [(consts [expr acc]
              (loop [stack [expr] acc acc]
                (if (empty? stack)
                  acc
                  (let [x (peek stack) stack (pop stack)]
                    (case (e/tag x)
                      :const (recur stack (conj acc (name/->string (e/const-name x))))
                      :app (recur (conj stack (e/app-fn x) (e/app-arg x)) acc)
                      :lam (recur (conj stack (e/lam-type x) (e/lam-body x)) acc)
                      :forall (recur (conj stack (e/forall-type x) (e/forall-body x)) acc)
                      :let (recur (conj stack (e/let-type x) (e/let-value x) (e/let-body x)) acc)
                      :mdata (recur (conj stack (e/mdata-expr x)) acc)
                      :proj (recur (conj stack (e/proj-struct x)) acc)
                      (recur stack acc))))))
            (visit [s]
              (when (.add seen s)
                (when-let [ci (env/lookup env (name/from-string s))]
                  (when (env/axiom? ci) (swap! axioms conj s))
                  (doseq [c (consts (env/ci-type ci) #{})] (visit c))
                  (when-let [v (env/ci-value ci)]
                    (doseq [c (consts v #{})] (visit c))))))]
      (visit (str label))
      @axioms)))

;; ## Generic quotient lifting
;;
;; `qc` describes a quotient of a type `:alpha : Type` by `:rel`, with
;; `:refl` (a ↦ proof of rel a a) and `:symm` ((a b h) ↦ proof of rel b a).
;; Operations and congruences are Clojure functions producing kernel terms.

(defn- quot-of [qc] (quot-type (:alpha qc) (:rel qc)))
(defn- mk-of [qc a] (quot-mk (:alpha qc) (:rel qc) a))
(defn- sound-of [qc a b h] (quot-sound (:alpha qc) (:rel qc) a b h))
(defn- rel-of [qc a b] (app (:rel qc) a b))

(defn lift1*
  "`Quot r → Quot r` lifting `op` (a ↦ term) with `congr` ((a b h) ↦ proof of
  `r (op a) (op b)`)."
  [qc op congr]
  (let [Qt (quot-of qc) A (:alpha qc)]
    (lam "x" Qt
         (fn [x]
           (app (quot-lift A (:rel qc) Qt
                           (lam "a" A #(mk-of qc (op %)))
                           (lam "a" A (fn [a] (lam "b" A (fn [b] (lam "h" (rel-of qc a b)
                                                                      #(sound-of qc (op a) (op b) (congr a b %))))))))
                x)))))

(defn quot-ind-all*
  "Proof of `P x₁ … xₙ` for the bound quotient variables `xs`, from `leaf`
  (representatives ↦ proof of `P (mk a₁) … (mk aₙ)`)."
  [qc xs motive leaf]
  (let [Qt (quot-of qc) A (:alpha qc)]
    (letfn [(go [done remaining]
              (if (empty? remaining)
                (leaf done)
                (app (quot-ind A (:rel qc)
                               (lam "x" Qt #(apply motive (concat (map (partial mk-of qc) done) [%] (rest remaining))))
                               (lam "a" A #(go (conj done %) (rest remaining))))
                     (first remaining))))]
      (go [] (vec xs)))))

(defn lift2*
  "`Quot r → Quot r → Quot r` lifting the binary `op` with `congr`
  ((a a' b b' ha hb) ↦ proof of `r (op a b) (op a' b')`)."
  [qc op congr]
  (let [Qt (quot-of qc) A (:alpha qc) refl (:refl qc)
        inner (fn [a y]
                (app (quot-lift A (:rel qc) Qt
                                (lam "b" A #(mk-of qc (op a %)))
                                (lam "b" A (fn [b] (lam "b'" A (fn [b'] (lam "h" (rel-of qc b b')
                                                                              #(sound-of qc (op a b) (op a b')
                                                                                         (congr a a b b' (refl a) %))))))))
                     y))]
    (lam "x" Qt
         (fn [x]
           (lam "y" Qt
                (fn [y]
                  (app (quot-lift A (:rel qc) Qt
                                  (lam "a" A #(inner % y))
                                  (lam "a" A
                                       (fn [a]
                                         (lam "a'" A
                                              (fn [a']
                                                (lam "h" (rel-of qc a a')
                                                     (fn [h]
                                                       (app (quot-ind A (:rel qc)
                                                                      (lam "z" Qt #(k/eq-at Qt u1 (inner a %) (inner a' %)))
                                                                      (lam "b" A #(sound-of qc (op a %) (op a' %)
                                                                                            (congr a a' % % h (refl %)))))
                                                            y))))))))
                       x)))))))
