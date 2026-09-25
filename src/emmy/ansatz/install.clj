#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.install
  "The single place where installation order and installation IO live.

  Every installing namespace exposes `install`: either a pure function from
  context to context, or a vector of steps built with [[pure]] and [[io]] when
  some of its work can only happen against the global environment (compiled
  functions defined through `ansatz.core/define-verified`). It adds only its
  own declarations, assuming the namespaces before it in [[ns-list]] are
  present. This namespace owns the order, runs the steps, and records a
  completed namespace as a marker constant in the environment, so installing
  again costs a lookup.

  A namespace may also define `register!`, an IO function for process-global
  state that is not part of the kernel environment (for example tactics). The
  `!` functions here run it first; [[register-all!]] runs every one, which is
  what a program working only with pure contexts needs.

  A marked namespace is not re-run, even if its code changed in a live REPL;
  new declarations need a fresh environment.

  ```clojure
  (install/install-all!)                                   ; everything, in order
  (install/install-through! 'emmy.ansatz.analysis.lagrange) ; one namespace and what it needs
  (install/install (k/base-ctx) (install/through ns))      ; pure: no global effect
  ```

  Namespaces are loaded on demand with `requiring-resolve`, so this namespace
  requires none of them and cannot participate in a require cycle."
  (:require [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.core :as k]))

(def ns-list
  "Installing namespaces in dependency order."
  '[emmy.ansatz.algebra
    emmy.ansatz.analysis.order
    emmy.ansatz.analysis.rational
    emmy.ansatz.expression
    emmy.ansatz.calculus
    emmy.ansatz.simplify
    emmy.ansatz.analysis.real
    emmy.ansatz.analysis.topology
    emmy.ansatz.analysis.qfield
    emmy.ansatz.analysis.reals
    emmy.ansatz.analysis.metric
    emmy.ansatz.analysis.real-topology
    emmy.ansatz.analysis.derivative
    emmy.ansatz.analysis.mathlib
    emmy.ansatz.analysis.lagrange
    emmy.ansatz.analysis.polynomial])

;; ## Steps

(defn pure
  "A step that extends a context: `f` is a function from context to context."
  [f]
  {:kind :pure :f f})

(defn io
  "A step that can only write the global environment: `f` takes no arguments."
  [f]
  {:kind :io :f f})

;; ## Markers

(defn- marker [ns-sym]
  (str "Emmy.Install." ns-sym))

(defn installed-ns?
  "True if the namespace `ns-sym` has been installed into the context."
  [ctx ns-sym]
  (k/installed? ctx (marker ns-sym)))

(defn- mark [ctx ns-sym]
  (if (installed-ns? ctx ns-sym)
    ctx
    (t/declare-constant ctx :def (marker ns-sym) t/prop (k/const "True"))))

;; ## Installers

(defn- resolve-in
  "The var `ns-sym/fn-sym`, loading the namespace if it isn't present yet. A
  namespace that cannot be loaded is reported with the load failure as its
  cause."
  [ns-sym fn-sym]
  (try
    (if (find-ns ns-sym)
      (ns-resolve ns-sym fn-sym)
      (requiring-resolve (symbol (str ns-sym) (str fn-sym))))
    (catch java.io.FileNotFoundException e
      (throw (ex-info "Namespace could not be loaded" {:ns ns-sym} e)))))

(defn installer
  "The install steps of the namespace `ns-sym`: its `install`, as a vector of
  [[pure]] and [[io]] steps."
  [ns-sym]
  (let [v (some-> (resolve-in ns-sym 'install) deref)]
    (cond
      (vector? v) v
      (fn? v) [(pure v)]
      :else (throw (ex-info "Namespace has no installer" {:ns ns-sym})))))

(defn register!
  "IO edge. Runs `ns-sym`'s `register!` if it has one (process-global state such
  as tactics; idempotent)."
  [ns-sym]
  (when-let [register (resolve-in ns-sym 'register!)]
    (register)))

(defn register-all!
  "IO edge. Runs every namespace's `register!`, without touching the kernel
  environment."
  []
  (run! register! ns-list))

(defn through
  "`ns-sym` preceded by every namespace it needs, in installation order."
  [ns-sym]
  (let [before (take-while #(not= % ns-sym) ns-list)]
    (when (= (count before) (count ns-list))
      (throw (ex-info "Namespace is not in ns-list" {:ns ns-sym})))
    (conj (vec before) ns-sym)))

;; ## Running

(defn- groups
  "`steps` as runs: each maximal sequence of pure steps composed into one
  pure step, IO steps left alone."
  [steps]
  (->> (partition-by :kind steps)
       (mapcat (fn [run]
                 (if (= :pure (:kind (first run)))
                   [(pure (apply comp (reverse (map :f run))))]
                   run)))))

(defn run-steps!
  "IO edge. Runs `steps` against the global environment under
  [[emmy.ansatz.core/install-lock]]. Each run of pure steps is committed at
  once (all or nothing); an IO step runs directly, and the next commit reads
  what it wrote. With `ns-sym`, the namespace's marker is committed together
  with the last pure run, so it never exists without its declarations."
  ([steps] (run-steps! steps nil))
  ([steps ns-sym]
   (let [steps (cond-> (vec (groups steps))
                 ns-sym (as-> s
                          (if (= :pure (:kind (peek s)))
                            (conj (pop s) (pure (comp #(mark % ns-sym) (:f (peek s)))))
                            (conj s (pure #(mark % ns-sym))))))]
     (locking k/install-lock
       (doseq [{:keys [kind f]} steps]
         (case kind
           :pure (k/commit! f)
           :io (f)))))))

(defn install
  "Pure. Extends `ctx` with the declarations of `nss`, in the given order,
  skipping namespaces already installed in it. Throws for a namespace that
  still needs IO (see [[io]]) and isn't installed yet."
  [ctx nss]
  (reduce (fn [ctx ns-sym]
            (if (installed-ns? ctx ns-sym)
              ctx
              (let [steps (installer ns-sym)]
                (when-let [step (first (filter #(= :io (:kind %)) steps))]
                  (throw (ex-info "Namespace needs IO to install; use install!"
                                  {:ns ns-sym :step step})))
                (mark (reduce (fn [ctx {:keys [f]}] (f ctx)) ctx steps) ns-sym))))
          ctx nss))

(defn install!
  "IO edge. Registers and installs one namespace into the global environment,
  unless it is already installed."
  [ns-sym]
  (register! ns-sym)
  (locking k/install-lock
    (when-not (installed-ns? (k/base-ctx) ns-sym)
      (run-steps! (installer ns-sym) ns-sym))))

(defn install-all!
  "IO edge. Installs every namespace in [[ns-list]] into the global environment."
  []
  (run! install! ns-list))

(defn install-through!
  "IO edge. Installs `ns-sym` and its prerequisites into the global environment."
  [ns-sym]
  (run! install! (through ns-sym)))
