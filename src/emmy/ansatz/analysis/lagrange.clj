#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.lagrange
  "Finite-dimensional derivatives and the Euler–Lagrange interface.

  Points of ℝⁿ are coordinate functions `Nat → R`, so a partial derivative is
  the ordinary derivative of a slice:

  ```
  Emmy.Analysis.Lagrange.update p i s      -- p with coordinate i replaced by s
  HasPartialDerivAt f i d p := HasDerivAt (fun s => f (update p i s)) d (p i)
  HasCurveDerivAt γ v t     := ∀ i, HasDerivAt (fun s => γ s i) (v i) t
  ```

  The Euler–Lagrange interface is stated for one degree of freedom:
  `ELPath P F` says the momentum `P = ∂L/∂v` along the path is differentiable
  with derivative the force `F = ∂L/∂q`, which is `d/dt (∂L/∂v) = ∂L/∂q`. The
  free particle is worked through: its momentum `m·v` is *derived* from the
  kinetic energy rather than assumed, and uniform motion is proved to satisfy
  the equation."
  (:require [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.derivative :as d]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.install :as registry]))

(def ^:private u (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.Lagrange.")

(defn- c [s] (k/const (str prefix s)))
(defn- rc [s] (k/const (str "Emmy.Analysis.R." s)))
(defn- dc [s] (k/const (str "Emmy.Analysis.Derivative." s)))

(def R r/R)
(def Nat (k/const "Nat"))
(def Pt "Points of ℝⁿ, as coordinate functions." (t/arrow Nat R))
(def FnR (t/arrow R R))
(def ^:private PtR (t/arrow Pt R))

(defn- eq [a b] (k/eq-at R u a b))
(defn- eq-nat [a b] (k/eq-at Nat u a b))
(defn- symm [ty a b h] (t/app (k/const "Eq.symm" u) ty a b h))

(def ^:private decl (t/declarer prefix))

(defn update' "`p` with coordinate `i` replaced by `s`." [p i s]
  (t/app (c "update") p i s))
(defn has-partial "`∂f/∂xᵢ = d` at the point `p`." [f i d p]
  (t/app (c "HasPartialDerivAt") f i d p))
(defn has-curve-deriv "The componentwise derivative of a curve." [g v x]
  (t/app (c "HasCurveDerivAt") g v x))
(defn el-path "`d/dt (∂L/∂v) = ∂L/∂q` along a path." [P F]
  (t/app (c "ELPath") P F))

;; ## Coordinates

(defn- install-coordinates [ctx]
  (-> ctx
  (decl :def "update" (t/>-> Pt Nat R Pt)
    (t/lambda [[p Pt] [i Nat] [s R] [j Nat]]
      (t/app (k/const "ite" u) R (eq-nat j i) (t/app (k/const "Nat.decEq") j i)
             s (t/app p j))))
  (decl :thm "update_same"
    (t/forall [[p Pt] [i Nat] [s R]] (eq (t/app (update' p i s) i) s))
    (t/lambda [[p Pt] [i Nat] [s R]]
      (t/app (k/const "if_pos" u) (eq-nat i i) (t/app (k/const "Nat.decEq") i i)
             (t/app (k/const "Eq.refl" u) Nat i) R s (t/app p i))))
  (decl :thm "update_other"
    (t/forall [[p Pt] [i Nat] [j Nat] [s R]]
      (t/arrow (t/not' (eq-nat j i)) (eq (t/app (update' p i s) j) (t/app p j))))
    (t/lambda [[p Pt] [i Nat] [j Nat] [s R] [h (t/not' (eq-nat j i))]]
      (t/app (k/const "if_neg" u) (eq-nat j i) (t/app (k/const "Nat.decEq") j i)
             h R s (t/app p j))))
  ;; replacing a coordinate by its own value changes nothing
  (decl :thm "update_self"
    (t/forall [[p Pt] [i Nat]] (k/eq-at Pt u (update' p i (t/app p i)) p))
    (t/lambda [[p Pt] [i Nat]]
      (t/app (k/const "funext" u u) Nat (t/lambda [[_j Nat]] R)
             (update' p i (t/app p i)) p
             (t/lambda [[j Nat]]
               (t/app (k/const "Decidable.byCases" level/zero)
                      (eq-nat j i)
                      (eq (t/app (update' p i (t/app p i)) j) (t/app p j))
                      (t/app (k/const "Nat.decEq") j i)
                      ;; j = i: both sides are p i
                      (t/lam "hji" (eq-nat j i)
                             (fn [hji]
                               (t/app (k/const "Eq.trans" u) R
                                      (t/app (update' p i (t/app p i)) j) (t/app p i) (t/app p j)
                                      (t/app (k/const "if_pos" u) (eq-nat j i)
                                             (t/app (k/const "Nat.decEq") j i) hji R
                                             (t/app p i) (t/app p j))
                                      (t/app (k/const "congrArg" u u) Nat R i j p
                                             (symm Nat j i hji)))))
                      (t/lam "hji" (t/not' (eq-nat j i))
                             #(t/app (c "update_other") p i j (t/app p i) %)))))))
  ;; a pointwise equal function has the same derivative
  (decl :thm "hasDerivAt_congr"
    (t/forall [[f FnR] [g FnR] [dv R] [x R]]
      (t/>-> (t/forall [[y R]] (eq (t/app f y) (t/app g y)))
             (d/has-deriv-at f dv x)
             (d/has-deriv-at g dv x)))
    (t/lambda [[f FnR] [g FnR] [dv R] [x R]
               [h (t/forall [[y R]] (eq (t/app f y) (t/app g y)))]
               [hf (d/has-deriv-at f dv x)]]
      (t/transport-at FnR u (t/lambda [[phi FnR]] (d/has-deriv-at phi dv x)) f g
                      (t/app (k/const "funext" u u) R (t/lambda [[_y R]] R) f g h)
                      hf)))))

;; ## Partial derivatives

(defn- install-partials [ctx]
  (-> ctx
  (decl :def "HasPartialDerivAt"
    (t/arrow PtR (t/arrow Nat (t/arrow R (t/arrow Pt t/prop))))
    (t/lambda [[f PtR] [i Nat] [dv R] [p Pt]]
      (d/has-deriv-at (t/lam "s" R #(t/app f (update' p i %))) dv (t/app p i))))
  ;; constants have vanishing partials
  (decl :thm "partial_const"
    (t/forall [[a R] [i Nat] [p Pt]]
      (has-partial (t/lam "q" Pt (fn [_] a)) i r/zero p))
    (t/lambda [[a R] [i Nat] [p Pt]]
      (t/app (dc "const") a (t/app p i))))
  ;; ∂xᵢ/∂xᵢ = 1
  (decl :thm "partial_proj_same"
    (t/forall [[i Nat] [p Pt]]
      (has-partial (t/lam "q" Pt #(t/app % i)) i r/one p))
    (t/lambda [[i Nat] [p Pt]]
      (let [slice (t/lam "s" R #(t/app (update' p i %) i))]
        (t/app (c "hasDerivAt_congr") (t/lam "y" R identity) slice r/one (t/app p i)
               (t/lambda [[y R]] (symm R (t/app (update' p i y) i) y
                                       (t/app (c "update_same") p i y)))
               (t/app (dc "id") (t/app p i))))))
  ;; ∂xⱼ/∂xᵢ = 0 for j ≠ i
  (decl :thm "partial_proj_other"
    (t/forall [[i Nat] [j Nat] [p Pt]]
      (t/arrow (t/not' (eq-nat j i))
               (has-partial (t/lam "q" Pt #(t/app % j)) i r/zero p)))
    (t/lambda [[i Nat] [j Nat] [p Pt] [h (t/not' (eq-nat j i))]]
      (let [slice (t/lam "s" R #(t/app (update' p i %) j))]
        (t/app (c "hasDerivAt_congr") (t/lam "y" R (fn [_] (t/app p j))) slice
               r/zero (t/app p i)
               (t/lambda [[y R]] (symm R (t/app (update' p i y) j) (t/app p j)
                                       (t/app (c "update_other") p i j y h)))
               (t/app (dc "const") (t/app p j) (t/app p i))))))
  ;; partials are additive: the slices add pointwise
  (decl :thm "partial_add"
    (t/forall [[f PtR] [g PtR] [df R] [dg R] [i Nat] [p Pt]]
      (t/arrow (has-partial f i df p)
               (t/arrow (has-partial g i dg p)
                        (has-partial (t/lam "q" Pt #(r/add (t/app f %) (t/app g %)))
                                     i (r/add df dg) p))))
    (t/lambda [[f PtR] [g PtR] [df R] [dg R] [i Nat] [p Pt]
               [hf (has-partial f i df p)] [hg (has-partial g i dg p)]]
      (t/app (dc "add")
             (t/lam "s" R #(t/app f (update' p i %)))
             (t/lam "s" R #(t/app g (update' p i %)))
             df dg (t/app p i) hf hg)))))

;; ## Curves into ℝⁿ

(defn- install-curves [ctx]
  (-> ctx
  (decl :def "HasCurveDerivAt"
    (t/arrow (t/arrow R Pt) (t/arrow Pt (t/arrow R t/prop)))
    (t/lambda [[g (t/arrow R Pt)] [v Pt] [x R]]
      (t/forall [[i Nat]] (d/has-deriv-at (t/lam "s" R #(t/app (t/app g %) i)) (t/app v i) x))))
  (decl :thm "curve_const"
    (t/forall [[p Pt] [x R]]
      (has-curve-deriv (t/lam "s" R (fn [_] p)) (t/lam "i" Nat (fn [_] r/zero)) x))
    (t/lambda [[p Pt] [x R] [i Nat]]
      (t/app (dc "const") (t/app p i) x)))
  (decl :thm "curve_add"
    (t/forall [[g (t/arrow R Pt)] [h (t/arrow R Pt)] [v Pt] [w Pt] [x R]]
      (t/arrow (has-curve-deriv g v x)
               (t/arrow (has-curve-deriv h w x)
                        (has-curve-deriv (t/lam "s" R (fn [s] (t/lam "i" Nat #(r/add (t/app (t/app g s) %)
                                                                                     (t/app (t/app h s) %)))))
                                         (t/lam "i" Nat #(r/add (t/app v %) (t/app w %)))
                                         x))))
    (t/lambda [[g (t/arrow R Pt)] [h (t/arrow R Pt)] [v Pt] [w Pt] [x R]
               [hg (has-curve-deriv g v x)] [hh (has-curve-deriv h w x)] [i Nat]]
      (t/app (dc "add")
             (t/lam "s" R #(t/app (t/app g %) i))
             (t/lam "s" R #(t/app (t/app h %) i))
             (t/app v i) (t/app w i) x (t/app hg i) (t/app hh i))))))

;; ## The Euler–Lagrange equation for one degree of freedom

(defn- install-ring
  "Pure. Declares the LagrangeRing identities `install-euler-lagrange`'s
  proofs rely on."
  [ctx]
  (-> ctx
      (r/ring-identity "LagrangeRing.square_value" '[v] '(+ (* 1 v) (* v 1)) '(+ v v))
      (r/ring-identity "LagrangeRing.scale_value" '[fx a df]
                       '(+ (* 0 fx) (* a df)) '(* a df))
      (r/ring-identity "LagrangeRing.kinetic_expand" '[h m w]
                       '(* (* h m) (+ w w)) '(+ (* h (* m w)) (* h (* m w))))
      (r/ring-identity "LagrangeRing.mul_zero" '[m] '(* m 0) '0)))

(defn- install-euler-lagrange [ctx]
  (-> ctx
  (decl :thm "scale"
    (t/forall [[a R] [f FnR] [df R] [x R]]
      (t/arrow (d/has-deriv-at f df x)
               (d/has-deriv-at (t/lam "y" R #(r/mul a (t/app f %))) (r/mul a df) x)))
    (t/lambda [[a R] [f FnR] [df R] [x R] [hf (d/has-deriv-at f df x)]]
      (let [k (t/lam "y" R (fn [_] a))
            value (r/add (r/mul r/zero (t/app f x)) (r/mul a df))]
        (t/transport-at R u
                        (t/lambda [[z R]] (d/has-deriv-at (t/lam "y" R #(r/mul a (t/app f %))) z x))
                        value (r/mul a df)
                        (t/app (rc "LagrangeRing.scale_value") (t/app f x) a df)
                        (t/app (dc "mul") k f r/zero df x (t/app (dc "const") a x) hf)))))
  ;; the momentum of the free particle is derived from its kinetic energy
  (decl :thm "kinetic_momentum"
    (t/forall [[m R] [v R]]
      (d/has-deriv-at (t/lam "w" R #(r/mul (r/mul r/half m) (r/mul % %))) (r/mul m v) v))
    (t/lambda [[m R] [v R]]
      (let [idf (t/lam "y" R identity)
            square (t/lam "y" R #(r/mul % %))
            hsq (t/transport-at R u (t/lambda [[z R]] (d/has-deriv-at square z v))
                                (r/add (r/mul r/one v) (r/mul v r/one)) (r/add v v)
                                (t/app (rc "LagrangeRing.square_value") v)
                                (t/app (dc "mul") idf idf r/one r/one v
                                       (t/app (dc "id") v) (t/app (dc "id") v)))
            scaled (t/app (c "scale") (r/mul r/half m) square (r/add v v) v hsq)]
        (t/transport-at R u
                        (t/lambda [[z R]] (d/has-deriv-at (t/lam "w" R #(r/mul (r/mul r/half m) (r/mul % %))) z v))
                        (r/mul (r/mul r/half m) (r/add v v)) (r/mul m v)
                        (t/app (k/const "Eq.trans" u) R
                               (r/mul (r/mul r/half m) (r/add v v))
                               (r/add (r/mul r/half (r/mul m v)) (r/mul r/half (r/mul m v)))
                               (r/mul m v)
                               (t/app (rc "LagrangeRing.kinetic_expand") r/half m v)
                               (t/app (rc "half_add_half") (r/mul m v)))
                        scaled))))
  ;; the free Lagrangian does not depend on position, so the force vanishes
  (decl :thm "kinetic_force"
    (t/forall [[m R] [v R] [q R]]
      (d/has-deriv-at (t/lam "y" R (fn [_] (r/mul (r/mul r/half m) (r/mul v v)))) r/zero q))
    (t/lambda [[m R] [v R] [q R]]
      (t/app (dc "const") (r/mul (r/mul r/half m) (r/mul v v)) q)))
  ;; d/dt (∂L/∂v) = ∂L/∂q along the path
  (decl :def "ELPath" (t/arrow FnR (t/arrow FnR t/prop))
    (t/lambda [[P FnR] [F FnR]]
      (t/forall [[x R]]
        (t/exists' R (t/lambda [[dP R]]
                       (t/and' (d/has-deriv-at P dP x) (eq dP (t/app F x))))))))
  ;; the momentum m·v of a path with acceleration a has derivative m·a
  (decl :thm "momentum_deriv"
    (t/forall [[m R] [v FnR] [a R] [x R]]
      (t/arrow (d/has-deriv-at v a x)
               (d/has-deriv-at (t/lam "s" R #(r/mul m (t/app v %))) (r/mul m a) x)))
    (t/lambda [[m R] [v FnR] [a R] [x R] [hv (d/has-deriv-at v a x)]]
      (t/app (c "scale") m v a x hv)))
  ;; uniform motion solves the Euler–Lagrange equation of the free particle
  (decl :thm "free_particle_uniform"
    (t/forall [[m R] [q FnR] [v FnR]]
      (t/arrow (t/forall [[x R]] (d/has-deriv-at q (t/app v x) x))
               (t/arrow (t/forall [[x R]] (d/has-deriv-at v r/zero x))
                        (el-path (t/lam "s" R #(r/mul m (t/app v %)))
                                 (t/lam "s" R (fn [_] r/zero))))))
    (t/lambda [[m R] [q FnR] [v FnR]
               [_hq (t/forall [[x R]] (d/has-deriv-at q (t/app v x) x))]
               [ha (t/forall [[x R]] (d/has-deriv-at v r/zero x))]
               [x R]]
      (let [P (t/lam "s" R #(r/mul m (t/app v %)))
            F (t/lam "s" R (fn [_] r/zero))
            body (fn [dP] (t/and' (d/has-deriv-at P dP x) (eq dP (t/app F x))))]
        (t/exists-intro R (t/lambda [[dP R]] (body dP)) (r/mul m r/zero)
                        (t/and-intro (d/has-deriv-at P (r/mul m r/zero) x)
                                     (eq (r/mul m r/zero) (t/app F x))
                                     (t/app (c "momentum_deriv") m v r/zero x (t/app ha x))
                                     (t/app (rc "LagrangeRing.mul_zero") m))))))))

(defn install
  "Pure. Declares finite-dimensional partial derivatives, curve derivatives
  and the one-degree-of-freedom Euler–Lagrange interface into `ctx`."
  [ctx]
  (-> ctx
      install-ring
      install-coordinates
      install-partials
      install-curves
      install-euler-lagrange))

(defn install!
  "Installs finite-dimensional partial derivatives, curve derivatives and the
  one-degree-of-freedom Euler–Lagrange interface. Idempotent."
  []
  (registry/install-through! 'emmy.ansatz.analysis.lagrange)
  :installed)
