#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.codegen
  "Code generation from the verified Ansatz AST down to Emmy.

  Values of `Emmy.PolyExpr` (see [[emmy.ansatz.expression]]) produced by
  verified Ansatz functions become Emmy symbolic expressions, ready for Emmy's
  simplifier, TeX rendering, Clerk viewers, mechanics, and so on. The
  translation is structural and doesn't simplify anything: the output is
  exactly the tree Ansatz computed, and simplification is Emmy's job."
  (:require [emmy.expression :as x]))

(defn ->form
  "The bare Emmy s-expression for the runtime `PolyExpr` `value`, with the
  variable rendered as `var`."
  [value var]
  (let [[tag a b] value]
    (case (long tag)
      0 a
      1 var
      2 (list '+ (->form a var) (->form b var))
      3 (list '* (->form a var) (->form b var))
      4 (list '- (->form a var)))))

(defn ->emmy
  "The Emmy symbolic expression for the runtime `PolyExpr` `value`, with the
  variable rendered as `var`."
  [value var]
  (let [form (->form value var)]
    (if (or (number? form) (symbol? form))
      form
      (x/make-literal ::x/numeric form))))
