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
  "The bare Emmy s-expression for the runtime `PolyExpr` `value`, with `X`
  rendered as `var`, `param j` as `(nth params j)` and `frac p q` as the
  ratio `p/(q+1)`."
  ([value var] (->form value var []))
  ([value var params]
   (let [[tag a b] value]
     (case (long tag)
       0 a
       1 var
       2 (list '+ (->form a var params) (->form b var params))
       3 (list '* (->form a var params) (->form b var params))
       4 (list '- (->form a var params))
       5 (nth params a)
       6 (/ a (inc b))))))

(defn ->emmy
  "The Emmy symbolic expression for the runtime `PolyExpr` `value`, with `X`
  rendered as `var` and `param j` as `(nth params j)`."
  ([value var] (->emmy value var []))
  ([value var params]
   (let [form (->form value var params)]
     (if (or (number? form) (symbol? form))
       form
       (x/make-literal ::x/numeric form)))))
