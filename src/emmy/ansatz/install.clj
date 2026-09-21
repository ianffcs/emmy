#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.install
  "The single place where installation order and installation IO live.

  Every installing namespace exposes a pure `install` function from context to
  context that adds only its own declarations, assuming the namespaces before
  it in [[ns-list]] are already present. It does not call other namespaces'
  installers. This namespace owns the order, and its `!` functions are the IO
  edges that publish a context to the global Ansatz environment.

  A namespace may also define `register!`, an IO function for process-global
  state that is not part of the kernel environment (for example tactics). The
  `!` functions here run it first; [[register-all!]] runs every one, which is
  what a program working only with pure contexts needs.

  ```clojure
  (install/install-all!)                                   ; everything, in order
  (install/install-through! 'emmy.ansatz.analysis.lagrange) ; one namespace and what it needs
  (install/install (k/base-ctx) (install/through ns))      ; pure: no global effect
  ```

  Namespaces are loaded on demand with `requiring-resolve`, so this namespace
  requires none of them and cannot participate in a require cycle."
  (:require [emmy.ansatz.core :as k]))

(def ns-list
  "Installing namespaces in dependency order."
  '[emmy.ansatz.algebra
    emmy.ansatz.analysis.order
    emmy.ansatz.analysis.rational
    emmy.ansatz.analysis.real
    emmy.ansatz.analysis.topology
    emmy.ansatz.analysis.qfield
    emmy.ansatz.analysis.reals
    emmy.ansatz.analysis.real-topology
    emmy.ansatz.analysis.derivative
    emmy.ansatz.analysis.lagrange
    emmy.ansatz.expression
    emmy.ansatz.calculus
    emmy.ansatz.analysis.polynomial
    emmy.ansatz.simplify])

(defn- resolve-in
  "The var `ns-sym/fn-sym`, loading the namespace if needed. A namespace that
  cannot be loaded is reported with the load failure as its cause."
  [ns-sym fn-sym]
  (try
    (requiring-resolve (symbol (str ns-sym) (str fn-sym)))
    (catch java.io.FileNotFoundException e
      (throw (ex-info "Namespace could not be loaded" {:ns ns-sym} e)))))

(defn installer
  "The context -> context installer of the namespace `ns-sym`.

  During the migration to pure installers, a namespace that still only has the
  old zero-argument `install!` is adapted: it is run for its effect on the
  global environment and the resulting global context is returned. That
  adapter ignores the context it is given."
  [ns-sym]
  (or (resolve-in ns-sym 'install)
      (when-let [legacy (resolve-in ns-sym 'install!)]
        (fn [_ctx] (legacy) (k/base-ctx)))
      (throw (ex-info "Namespace has no installer" {:ns ns-sym}))))

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

(defn install
  "Pure. Extends `ctx` with the declarations of `nss`, in the given order."
  [ctx nss]
  (reduce (fn [ctx ns-sym] ((installer ns-sym) ctx)) ctx nss))

(defn install!
  "IO edge. Registers and installs one namespace into the global environment."
  [ns-sym]
  (register! ns-sym)
  (k/commit! (installer ns-sym)))

(defn install-all!
  "IO edge. Installs every namespace in [[ns-list]] into the global environment."
  []
  (run! install! ns-list))

(defn install-through!
  "IO edge. Installs `ns-sym` and its prerequisites into the global environment."
  [ns-sym]
  (run! install! (through ns-sym)))
