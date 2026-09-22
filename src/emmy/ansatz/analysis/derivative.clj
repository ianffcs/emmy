#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.derivative
  "Analytic derivatives over Emmy's constructed reals, checked by Ansatz.
  The difference-quotient limit is used; no numeric approximations are proofs."
  (:require [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.core :as k]))

(def ^:private u (level/succ level/zero))
(def R r/R)
(def FnR (t/arrow R R))
(def ^:private prefix "Emmy.Analysis.Derivative.")
(defn- c [s]
  (k/const (str prefix s)))

(defn- rc [s]
  (k/const (str "Emmy.Analysis.R." s)))

(defn- ring [s & args]
  (apply t/app (rc (str "DerivativeRing." s)) args))

(defn- eq [a b]
  (k/eq-at R u a b))

(defn- symm [a b h]
  (t/app (k/const "Eq.symm" u) R a b h))

(defn- pos [x]
  (r/lt r/zero x))

(defn- distance [a b]
  (r/abs (r/sub a b)))

(defn slope [f x]
  (t/app (c "slope") f x))

(defn has-deriv-at
  "Kernel proposition: f has derivative d at x."
  [f d x]
  (t/app (c "HasDerivAt") f d x))
(def ^:private decl (t/declarer prefix))
(defn- body [f x L eps d]
  (t/forall [[y R]]
    (t/arrow (pos (distance y x))
             (t/arrow (r/lt (distance y x) d) (r/lt (distance (t/app f y) L) eps)))))
(defn- near-predicate [f x L eps]
  (t/lambda [[d R]] (t/and' (pos d) (body f x L eps d))))
(defn- near [f x L eps] (t/exists' R (near-predicate f x L eps)))
(defn- near-elim [f x L eps goal h next-proof]
  (t/exists-elim R (near-predicate f x L eps) goal h
    (t/lambda [[d R] [hd (t/and' (pos d) (body f x L eps d))]]
      (next-proof d (t/and-left (pos d) (body f x L eps d) hd)
                  (t/and-right (pos d) (body f x L eps d) hd)))))
(defn- near-intro [f x L eps d hd hall]
  (t/exists-intro R (near-predicate f x L eps) d
    (t/and-intro (pos d) (body f x L eps d) hd hall)))

(defn- install-algebra! []
  (doseq [[label vars lhs rhs]
          [["slope_const" '[a b] '(* (- a a) b) 0]
           ["slope_add" '[a b c d h] '(* (- (+ a c) (+ b d)) h)
            '(+ (* (- a b) h) (* (- c d) h))]
           ["slope_neg" '[a b h] '(* (- (- a) (- b)) h) '(- (* (- a b) h))]
           ["slope_mul" '[a b c d h] '(* (- (* a c) (* b d)) h)
            '(+ (* (* (- a b) h) c) (* b (* (- c d) h)))]
           ["cancel_reorder" '[a b h] '(* (* a h) b) '(* (* b h) a)]
           ["reconstruct_reorder" '[a b h v] '(+ b (* h (* (- a b) v)))
            '(+ b (* (* (- a b) v) h))]
           ["reconstruct_add" '[a b] '(+ b (- a b)) 'a]
           ["limit_reconstruct" '[a d] '(+ a (* 0 d)) 'a]
           ["sub_eq_add" '[a b] '(- a b) '(+ a (- b))]
           ["scale_difference" '[a b c] '(* (- b a) c) '(- (* b c) (* a c))]
           ["scale_cancel" '[a c v] '(* (* a c) v) '(* c (* v a))]
           ["error_expand" '[a b d h v] '(* (- (* (- a b) v) d) h)
            '(- (* (* (- a b) v) h) (* d h))]
           ["residual_self" '[a b d] '(- (- a a) (* d (- b b))) 0]
           ["tolerance_cancel_left" '[a v e h] '(* (* v e) (* a h)) '(* (* a (* v e)) h)]
           ["tolerance_cancel_right" '[a v e h] '(* a (* (* v e) h)) '(* (* a (* v e)) h)]
           ["factor_sum" '[e h] '(+ (* e h) (* e h)) '(* (+ e e) h)]
           ["chain_error" '[a c df dg h]
            '(+ (- a (* df c)) (* df (- c (* dg h)))) '(- a (* (* df dg) h))]]]
    (r/ring-identity! (str "DerivativeRing." label) vars lhs rhs)))

(defn- install-limit-tools [ctx]
  (-> ctx
    (decl :thm "step_ne_zero"
    (t/forall [[x R] [y R]]
      (t/arrow (pos (distance y x)) (t/not' (eq (r/sub y x) r/zero))))
    (t/lambda [[x R] [y R] [h (pos (distance y x))] [hz (eq (r/sub y x) r/zero)]]
      (let [xy (t/app (rc "eq_of_sub_eq_zero") x y hz)
            hy (t/transport-at R u (t/lambda [[z R]] (pos (distance y z))) x y xy h)
            impossible (t/transport-at R u (t/lambda [[z R]] (pos z))
                         (distance y y) r/zero (t/app (rc "abs_sub_self") y) hy)]
        (t/app (rc "lt_irrefl") r/zero impossible))))
  (decl :thm "tendsto_congr"
    (t/forall [[f FnR] [g FnR] [x R] [L R]]
      (t/arrow (t/forall [[y R]] (t/arrow (pos (distance y x)) (eq (t/app f y) (t/app g y))))
        (t/arrow (r/tends-to-at f x L) (r/tends-to-at g x L))))
    (t/lambda [[f FnR] [g FnR] [x R] [L R]
               [heq (t/forall [[y R]] (t/arrow (pos (distance y x)) (eq (t/app f y) (t/app g y))))]
               [hf (r/tends-to-at f x L)] [eps R] [he (pos eps)]]
      (t/with-cont [[d hd hall] (near-elim f x L eps (near g x L eps) (t/app hf eps he))]
        (near-intro g x L eps d hd
          (t/lambda [[y R] [hy0 (pos (distance y x))] [hy (r/lt (distance y x) d)]]
            (t/transport-at R u (t/lambda [[z R]] (r/lt (distance z L) eps))
              (t/app f y) (t/app g y) (t/app heq y hy0) (t/app hall y hy0 hy)))))))
  (decl :thm "divide_mul_cancel"
    (t/forall [[a R] [b R]]
      (t/arrow (t/not' (eq b r/zero)) (eq (r/mul (r/mul a (r/inv b)) b) a)))
    (t/lambda [[a R] [b R] [hb (t/not' (eq b r/zero))]]
      (let [lhs (r/mul (r/mul a (r/inv b)) b)
            mid (r/mul (r/mul b (r/inv b)) a)
            right (r/mul r/one a)
            h1 (ring "cancel_reorder" a b (r/inv b))
            h2 (t/app (rc "mul_congr_fst") a (r/mul b (r/inv b)) r/one
                      (t/app (rc "mul_inv_cancel") b hb))]
        (t/app (k/const "Eq.trans" u) R lhs mid a h1
          (t/app (k/const "Eq.trans" u) R mid right a h2 (t/app (rc "one_mul") a))))))))

(defn- install-elementary [ctx]
  (-> ctx
  (decl :def "slope" (t/arrow FnR (t/arrow R FnR))
    (t/lambda [[f FnR] [x R] [y R]]
      (r/mul (r/sub (t/app f y) (t/app f x)) (r/inv (r/sub y x)))))
  (decl :def "HasDerivAt" (t/arrow FnR (t/arrow R (t/arrow R t/prop)))
    (t/lambda [[f FnR] [d R] [x R]] (r/tends-to-at (slope f x) x d)))
  (decl :thm "unique"
    (t/forall [[f FnR] [d R] [e R] [x R]]
      (t/arrow (has-deriv-at f d x) (t/arrow (has-deriv-at f e x) (eq d e))))
    (t/lambda [[f FnR] [d R] [e R] [x R]
               [hd (has-deriv-at f d x)] [he (has-deriv-at f e x)]]
      (t/app (rc "tendsto_unique") (slope f x) x d e hd he)))
  (decl :thm "const"
    (t/forall [[a R] [x R]] (has-deriv-at (t/lam "y" R (fn [_] a)) r/zero x))
    (t/lambda [[a R] [x R]]
      (let [f (t/lam "y" R (fn [_] a)) z (t/lam "y" R (fn [_] r/zero))]
        (t/app (c "tendsto_congr") z (slope f x) x r/zero
          (t/lambda [[y R] [_hy (pos (distance y x))]]
            (symm (t/app (slope f x) y) r/zero (ring "slope_const" a (r/inv (r/sub y x)))))
          (t/app (rc "tendsto_const") r/zero x)))))
  (decl :thm "id"
    (t/forall [[x R]] (has-deriv-at (t/lam "y" R identity) r/one x))
    (t/lambda [[x R]]
      (let [f (t/lam "y" R identity) one-fn (t/lam "y" R (fn [_] r/one))]
        (t/app (c "tendsto_congr") one-fn (slope f x) x r/one
          (t/lambda [[y R] [hy (pos (distance y x))]]
            (symm (t/app (slope f x) y) r/one
              (t/app (rc "mul_inv_cancel") (r/sub y x) (t/app (c "step_ne_zero") x y hy))))
          (t/app (rc "tendsto_const") r/one x)))))
  (decl :thm "add"
    (t/forall [[f FnR] [g FnR] [df R] [dg R] [x R]]
      (t/arrow (has-deriv-at f df x) (t/arrow (has-deriv-at g dg x)
        (has-deriv-at (t/lambda [[y R]] (r/add (t/app f y) (t/app g y))) (r/add df dg) x))))
    (t/lambda [[f FnR] [g FnR] [df R] [dg R] [x R]
               [hf (has-deriv-at f df x)] [hg (has-deriv-at g dg x)]]
      (let [h (t/lambda [[y R]] (r/add (t/app f y) (t/app g y)))
            sum (t/lambda [[y R]] (r/add (t/app (slope f x) y) (t/app (slope g x) y)))]
        (t/app (c "tendsto_congr") sum (slope h x) x (r/add df dg)
          (t/lambda [[y R] [_hy (pos (distance y x))]]
            (symm (t/app (slope h x) y) (t/app sum y)
              (ring "slope_add" (t/app f y) (t/app f x) (t/app g y) (t/app g x) (r/inv (r/sub y x)))))
          (t/app (rc "tendsto_add") (slope f x) (slope g x) x df dg hf hg)))))
  (decl :thm "neg"
    (t/forall [[f FnR] [df R] [x R]]
      (t/arrow (has-deriv-at f df x)
        (has-deriv-at (t/lambda [[y R]] (r/neg (t/app f y))) (r/neg df) x)))
    (t/lambda [[f FnR] [df R] [x R] [hf (has-deriv-at f df x)]]
      (let [h (t/lambda [[y R]] (r/neg (t/app f y)))
            negative (t/lambda [[y R]] (r/neg (t/app (slope f x) y)))]
        (t/app (c "tendsto_congr") negative (slope h x) x (r/neg df)
          (t/lambda [[y R] [_hy (pos (distance y x))]]
            (symm (t/app (slope h x) y) (t/app negative y)
              (ring "slope_neg" (t/app f y) (t/app f x) (r/inv (r/sub y x)))))
          (t/app (rc "tendsto_neg") (slope f x) x df hf)))))))

(defn- install-product [ctx]
  (-> ctx
  (decl :thm "tendsto_step"
    (t/forall [[x R]] (r/tends-to-at (t/lambda [[y R]] (r/sub y x)) x r/zero))
    (t/lambda [[x R]]
      (let [id (t/lam "y" R identity)
            constant (t/lam "y" R (fn [_] x))
            negative (t/lam "y" R (fn [_] (r/neg x)))
            step (t/lambda [[y R]] (r/sub y x))
            hn (t/app (rc "tendsto_neg") constant x x (t/app (rc "tendsto_const") x x))
            hs (t/app (rc "tendsto_add") id negative x x (r/neg x)
                      (t/app (rc "tendsto_id") x) hn)]
        (t/transport-at R u (t/lambda [[L R]] (r/tends-to-at step x L))
          (r/sub x x) r/zero (t/app (rc "sub_self") x) hs))))
  (decl :thm "reconstruct"
    (t/forall [[f FnR] [x R] [y R]]
      (t/arrow (pos (distance y x))
        (eq (r/add (t/app f x) (r/mul (r/sub y x) (t/app (slope f x) y))) (t/app f y))))
    (t/lambda [[f FnR] [x R] [y R] [hy (pos (distance y x))]]
      (let [a (t/app f y) b (t/app f x) h (r/sub y x)
            divided (r/mul (r/mul (r/sub a b) (r/inv h)) h)
            lhs (r/add b (r/mul h (t/app (slope f x) y)))
            middle (r/add b divided) last (r/add b (r/sub a b))
            hc (t/app (c "divide_mul_cancel") (r/sub a b) h (t/app (c "step_ne_zero") x y hy))
            congr (t/app (k/const "congrArg" u u) R R divided (r/sub a b)
                         (t/lambda [[z R]] (r/add b z)) hc)]
        (t/app (k/const "Eq.trans" u) R lhs middle a
          (ring "reconstruct_reorder" a b h (r/inv h))
          (t/app (k/const "Eq.trans" u) R middle last a congr (ring "reconstruct_add" a b))))))
  (decl :thm "tendsto_of_hasDerivAt"
    (t/forall [[f FnR] [d R] [x R]]
      (t/arrow (has-deriv-at f d x) (r/tends-to-at f x (t/app f x))))
    (t/lambda [[f FnR] [d R] [x R] [hf (has-deriv-at f d x)]]
      (let [fx (t/app f x)
            constant (t/lam "y" R (fn [_] fx))
            step (t/lambda [[y R]] (r/sub y x))
            product (t/lambda [[y R]] (r/mul (t/app step y) (t/app (slope f x) y)))
            reconstructed (t/lambda [[y R]] (r/add fx (t/app product y)))
            hp (t/app (rc "tendsto_mul") step (slope f x) x r/zero d
                      (t/app (c "tendsto_step") x) hf)
            hs (t/app (rc "tendsto_add") constant product x fx (r/mul r/zero d)
                      (t/app (rc "tendsto_const") fx x) hp)
            limit (t/transport-at R u (t/lambda [[L R]] (r/tends-to-at reconstructed x L))
                    (r/add fx (r/mul r/zero d)) fx (ring "limit_reconstruct" fx d) hs)]
        (t/app (c "tendsto_congr") reconstructed f x fx
          (t/lambda [[y R] [hy (pos (distance y x))]] (t/app (c "reconstruct") f x y hy)) limit))))
  (decl :thm "continuousAt"
    (t/forall [[f FnR] [d R] [x R]]
      (t/arrow (has-deriv-at f d x) (r/continuous-at f x)))
    (t/lambda [[f FnR] [d R] [x R] [hf (has-deriv-at f d x)]]
      (t/app (rc "continuousAt_of_tendsto") f x (t/app (c "tendsto_of_hasDerivAt") f d x hf))))
  (decl :thm "mul"
    (t/forall [[f FnR] [g FnR] [df R] [dg R] [x R]]
      (t/arrow (has-deriv-at f df x) (t/arrow (has-deriv-at g dg x)
        (has-deriv-at (t/lambda [[y R]] (r/mul (t/app f y) (t/app g y)))
                     (r/add (r/mul df (t/app g x)) (r/mul (t/app f x) dg)) x))))
    (t/lambda [[f FnR] [g FnR] [df R] [dg R] [x R]
               [hf (has-deriv-at f df x)] [hg (has-deriv-at g dg x)]]
      (let [h (t/lambda [[y R]] (r/mul (t/app f y) (t/app g y)))
            fx (t/app f x) gx (t/app g x)
            cf (t/lam "y" R (fn [_] fx))
            left (t/lambda [[y R]] (r/mul (t/app (slope f x) y) (t/app g y)))
            right (t/lambda [[y R]] (r/mul fx (t/app (slope g x) y)))
            sum (t/lambda [[y R]] (r/add (t/app left y) (t/app right y)))
            dl (r/mul df gx) dr (r/mul fx dg)
            hl (t/app (rc "tendsto_mul") (slope f x) g x df gx hf
                      (t/app (c "tendsto_of_hasDerivAt") g dg x hg))
            hr (t/app (rc "tendsto_mul") cf (slope g x) x fx dg
                      (t/app (rc "tendsto_const") fx x) hg)]
        (t/app (c "tendsto_congr") sum (slope h x) x (r/add dl dr)
          (t/lambda [[y R] [_hy (pos (distance y x))]]
            (symm (t/app (slope h x) y) (t/app sum y)
              (ring "slope_mul" (t/app f y) fx (t/app g y) gx (r/inv (r/sub y x)))))
          (t/app (rc "tendsto_add") left right x dl dr hl hr)))))))

(defn- install-scaling [ctx]
  (-> ctx
  (decl :thm "mul_lt_mul_right"
    (t/forall [[a R] [b R] [s R]]
      (t/arrow (r/lt a b) (t/arrow (pos s) (r/lt (r/mul a s) (r/mul b s)))))
    (t/lambda [[a R] [b R] [s R] [hab (r/lt a b)] [hs (pos s)]]
      (let [diff (r/sub b a) product (r/mul diff s)
            hp (t/app (rc "mul_pos") diff s (t/app (rc "lt_zero_of_positive") diff hab) hs)]
        (t/transport-at R u (t/lambda [[z R]] (r/positive z)) product
          (r/sub (r/mul b s) (r/mul a s)) (ring "scale_difference" a b s)
          (t/app (rc "positive_of_lt_zero") product hp)))))
  (decl :thm "scale_cancel"
    (t/forall [[a R] [s R]]
      (t/arrow (pos s) (eq (r/mul (r/mul a s) (r/inv s)) a)))
    (t/lambda [[a R] [s R] [hs (pos s)]]
      (t/app (k/const "Eq.trans" u) R (r/mul (r/mul a s) (r/inv s))
        (r/mul s (r/mul (r/inv s) a)) a (ring "scale_cancel" a s (r/inv s))
        (t/app (rc "mul_inv_mul") s a hs))))
  (decl :thm "lt_of_mul_lt_mul_right"
    (t/forall [[a R] [b R] [s R]]
      (t/arrow (r/lt (r/mul a s) (r/mul b s)) (t/arrow (pos s) (r/lt a b))))
    (t/lambda [[a R] [b R] [s R] [hab (r/lt (r/mul a s) (r/mul b s))] [hs (pos s)]]
      (let [left (r/mul (r/mul a s) (r/inv s))
            right (r/mul (r/mul b s) (r/inv s))
            scaled (t/app (c "mul_lt_mul_right") (r/mul a s) (r/mul b s) (r/inv s)
                     hab (t/app (rc "inv_pos") s hs))
            hleft (t/transport-at R u (t/lambda [[z R]] (r/lt z right)) left a
                    (t/app (c "scale_cancel") a s hs) scaled)]
        (t/transport-at R u (t/lambda [[z R]] (r/lt a z)) right b
          (t/app (c "scale_cancel") b s hs) hleft))))))

(defn remainder "The first-order residual at y: f(y)-f(x)-d*(y-x)." [f d x y]
  (r/sub (r/sub (t/app f y) (t/app f x)) (r/mul d (r/sub y x))))
(defn- residual-body [f d x eps delta]
  (t/forall [[y R]]
    (t/arrow (pos (distance y x))
      (t/arrow (r/lt (distance y x) delta)
        (r/lt (r/abs (remainder f d x y)) (r/mul eps (distance y x)))))))
(defn- residual-predicate [f d x eps]
  (t/lambda [[delta R]] (t/and' (pos delta) (residual-body f d x eps delta))))

(defn- install-remainder [ctx]
  (-> ctx
  (decl :def "RemainderBound" (t/arrow FnR (t/arrow R (t/arrow R t/prop)))
    (t/lambda [[f FnR] [d R] [x R]]
      (t/forall [[eps R]]
        (t/arrow (pos eps) (t/exists' R (residual-predicate f d x eps))))))
  (decl :thm "abs_remainder"
    (t/forall [[f FnR] [d R] [x R] [y R]]
      (t/arrow (pos (distance y x))
        (eq (r/abs (remainder f d x y))
            (r/mul (distance (t/app (slope f x) y) d) (distance y x)))))
    (t/lambda [[f FnR] [d R] [x R] [y R] [hy (pos (distance y x))]]
      (let [a (t/app f y) b (t/app f x) h (r/sub y x)
            err (r/sub (t/app (slope f x) y) d)
            lhs (r/mul err h)
            divided (r/mul (r/mul (r/sub a b) (r/inv h)) h)
            middle (r/sub divided (r/mul d h))
            residual (remainder f d x y)
            cancel (t/app (c "divide_mul_cancel") (r/sub a b) h (t/app (c "step_ne_zero") x y hy))
            e1 (ring "error_expand" a b d h (r/inv h))
            e2 (t/app (k/const "congrArg" u u) R R divided (r/sub a b)
                 (t/lambda [[z R]] (r/sub z (r/mul d h))) cancel)
            e (t/app (k/const "Eq.trans" u) R lhs middle residual e1 e2)
            abs-e (t/app (k/const "congrArg" u u) R R residual lhs (rc "abs") (symm lhs residual e))]
        (t/app (k/const "Eq.trans" u) R (r/abs residual) (r/abs lhs)
          (r/mul (r/abs err) (r/abs h)) abs-e (t/app (rc "abs_mul") err h)))))
  (decl :thm "remainder_iff"
    (t/forall [[f FnR] [d R] [x R]]
      (t/iff (has-deriv-at f d x) (t/app (c "RemainderBound") f d x)))
    (t/lambda [[f FnR] [d R] [x R]]
      (t/iff-intro (has-deriv-at f d x) (t/app (c "RemainderBound") f d x)
        (t/lambda [[hf (has-deriv-at f d x)] [eps R] [he (pos eps)]]
          (let [p (residual-predicate f d x eps) goal (t/exists' R p)]
            (t/with-cont [[delta hd hall] (near-elim (slope f x) x d eps goal (t/app hf eps he))]
              (t/exists-intro R p delta
                (t/and-intro (pos delta) (residual-body f d x eps delta) hd
                  (t/lambda [[y R] [hy0 (pos (distance y x))] [hy (r/lt (distance y x) delta)]]
                    (let [scaled (t/app (c "mul_lt_mul_right") (distance (t/app (slope f x) y) d)
                                   eps (distance y x) (t/app hall y hy0 hy) hy0)
                          residual (r/abs (remainder f d x y))
                          product (r/mul (distance (t/app (slope f x) y) d) (distance y x))]
                      (t/transport-at R u (t/lambda [[z R]] (r/lt z (r/mul eps (distance y x))))
                        product residual (symm residual product (t/app (c "abs_remainder") f d x y hy0)) scaled))))))))
        (t/lambda [[hf (t/app (c "RemainderBound") f d x)] [eps R] [he (pos eps)]]
          (t/exists-elim R (residual-predicate f d x eps) (near (slope f x) x d eps)
            (t/app hf eps he)
            (t/lambda [[delta R] [hd (t/and' (pos delta) (residual-body f d x eps delta))]]
              (let [hpos (t/and-left (pos delta) (residual-body f d x eps delta) hd)
                    hall (t/and-right (pos delta) (residual-body f d x eps delta) hd)]
                (near-intro (slope f x) x d eps delta hpos
                  (t/lambda [[y R] [hy0 (pos (distance y x))] [hy (r/lt (distance y x) delta)]]
                    (let [residual (r/abs (remainder f d x y))
                          product (r/mul (distance (t/app (slope f x) y) d) (distance y x))
                          hscaled (t/transport-at R u (t/lambda [[z R]] (r/lt z (r/mul eps (distance y x))))
                                    residual product (t/app (c "abs_remainder") f d x y hy0)
                                    (t/app hall y hy0 hy))]
                      (t/app (c "lt_of_mul_lt_mul_right") (distance (t/app (slope f x) y) d)
                        eps (distance y x) hscaled hy0)))))))))))))

(defn- residual-proof [f d x h]
  (t/app (k/const "Iff.mp") (has-deriv-at f d x) (t/app (c "RemainderBound") f d x)
    (t/app (c "remainder_iff") f d x) h))

(defn- residual-elim [f d x eps goal h next-proof]
  (t/exists-elim R (residual-predicate f d x eps) goal h
    (t/lambda [[delta R] [hd (t/and' (pos delta) (residual-body f d x eps delta))]]
      (next-proof delta (t/and-left (pos delta) (residual-body f d x eps delta) hd)
        (t/and-right (pos delta) (residual-body f d x eps delta) hd)))))

(defn- continuous-elim [f x eps goal h next-proof]
  (let [body (fn [delta]
               (t/forall [[y R]]
                 (t/arrow (r/lt (distance y x) delta) (r/lt (distance (t/app f y) (t/app f x)) eps))))
        p (t/lambda [[delta R]] (t/and' (pos delta) (body delta)))]
    (t/exists-elim R p goal h
      (t/lambda [[delta R] [hd (t/and' (pos delta) (body delta))]]
        (next-proof delta (t/and-left (pos delta) (body delta) hd)
          (t/and-right (pos delta) (body delta) hd))))))

(defn- smaller-elim [a b ha hb goal next-proof]
  (let [bounds (fn [d] (t/and' (r/lt d a) (r/lt d b)))
        p (t/lambda [[d R]] (t/and' (pos d) (bounds d)))]
    (t/exists-elim R p goal (t/app (rc "exists_pos_lt_both") a b ha hb)
      (t/lambda [[d R] [hd (t/and' (pos d) (bounds d))]]
        (let [h (t/and-right (pos d) (bounds d) hd)]
          (next-proof d (t/and-left (pos d) (bounds d) hd)
            (t/and-left (r/lt d a) (r/lt d b) h)
            (t/and-right (r/lt d a) (r/lt d b) h)))))))

(defn- scale-left-lt [a b s hab hs]
  (let [raw (t/app (c "mul_lt_mul_right") a b s hab hs)
        left (t/transport-at R u (t/lambda [[z R]] (r/lt z (r/mul b s)))
               (r/mul a s) (r/mul s a) (t/app (rc "mul_comm") a s) raw)]
    (t/transport-at R u (t/lambda [[z R]] (r/lt (r/mul s a) z))
      (r/mul b s) (r/mul s b) (t/app (rc "mul_comm") b s) left)))

(defn- tolerance-eq [side a e h ha]
  (let [tol (r/mul (r/inv a) e)
        lhs (if (= side :left) (r/mul tol (r/mul a h)) (r/mul a (r/mul tol h)))
        mid (r/mul (r/mul a tol) h)]
    (t/app (k/const "Eq.trans" u) R lhs mid (r/mul e h)
      (ring (if (= side :left) "tolerance_cancel_left" "tolerance_cancel_right") a (r/inv a) e h)
      (t/app (rc "mul_congr_fst") h (r/mul a tol) e (t/app (rc "mul_inv_mul") a e ha)))))

(defn- chain-estimate
  [f g df dg x y eps he hy0 _delta-outer hall-outer inner-bound slope-bound outer-close]
  (let [gx (t/app g x) gy (t/app g y) h (r/sub y x) ah (distance y x)
        e2 (r/mul r/half eps) he2 (t/app (rc "half_pos") eps he)
        A (r/add (r/abs dg) r/one) B (r/add (r/abs df) r/one)
        hA (t/app (rc "abs_add_one_pos") dg) hB (t/app (rc "abs_add_one_pos") df)
        ea (r/mul (r/inv A) e2) eb (r/mul (r/inv B) e2)
        hea (t/app (rc "mul_pos") (r/inv A) e2 (t/app (rc "inv_pos") A hA) he2)
        bound (r/mul e2 ah)
        hbound (t/app (rc "mul_pos") e2 ah he2 hy0)
        outer-error (remainder f df gx gy) inner-error (remainder g dg x y)
        outer-goal (r/lt (r/abs outer-error) bound)
        ;; |g y - g x| < (|dg|+1)*|y-x|, using the bounded difference quotient.
        sg (t/app (slope g x) y)
        sg-bound (t/app (rc "abs_lt_add") dg sg r/one slope-bound)
        scaled (t/app (c "mul_lt_mul_right") (r/abs sg) A ah sg-bound hy0)
        cancelled (t/app (c "divide_mul_cancel") (r/sub gy gx) h (t/app (c "step_ne_zero") x y hy0))
        abs-cancel (t/app (k/const "congrArg" u u) R R (r/sub gy gx) (r/mul sg h) (rc "abs")
                     (symm (r/mul sg h) (r/sub gy gx) cancelled))
        increment-eq (t/app (k/const "Eq.trans" u) R (distance gy gx) (r/abs (r/mul sg h))
                       (r/mul (r/abs sg) ah) abs-cancel (t/app (rc "abs_mul") sg h))
        increment-bound (t/transport-at R u (t/lambda [[z R]] (r/lt z (r/mul A ah)))
                          (r/mul (r/abs sg) ah) (distance gy gx)
                          (symm (distance gy gx) (r/mul (r/abs sg) ah) increment-eq) scaled)
        outer-bound
        (t/app (k/const "Classical.byCases") (eq gy gx) outer-goal
          (t/lambda [[same (eq gy gx)]]
            (let [at-self (remainder f df gx gx)
                  e0 (ring "residual_self" (t/app f gx) gx df)
                  ae0 (t/app (k/const "congrArg" u u) R R at-self r/zero (rc "abs") e0)
                  a0 (t/app (k/const "Eq.trans" u) R (r/abs at-self) (r/abs r/zero) r/zero ae0 (rc "abs_zero"))
                  self-bound (t/transport-at R u (t/lambda [[z R]] (r/lt z bound))
                               r/zero (r/abs at-self) (symm (r/abs at-self) r/zero a0) hbound)]
              (t/transport-at R u (t/lambda [[z R]] (r/lt (r/abs (remainder f df gx z)) bound))
                gx gy (symm gy gx same) self-bound)))
          (t/lambda [[different (t/not' (eq gy gx))]]
            (let [hp (t/app (rc "abs_pos_of_ne") gy gx different)
                  outer (t/app hall-outer gy hp outer-close)
                  scaled-bound (scale-left-lt (distance gy gx) (r/mul A ah) ea increment-bound hea)
                  both (t/app (rc "lt_trans") (r/abs outer-error) (r/mul ea (distance gy gx))
                         (r/mul ea (r/mul A ah)) outer scaled-bound)]
              (t/transport-at R u (t/lambda [[z R]] (r/lt (r/abs outer-error) z))
                (r/mul ea (r/mul A ah)) bound (tolerance-eq :left A e2 ah hA) both))))
        multiplied (t/app (rc "abs_mul_lt") df inner-error B (r/mul eb ah)
                     (t/app (rc "abs_lt_abs_add_one") df) inner-bound)
        inner-scaled (t/transport-at R u (t/lambda [[z R]] (r/lt (r/abs (r/mul df inner-error)) z))
                       (r/mul B (r/mul eb ah)) bound (tolerance-eq :right B e2 ah hB) multiplied)
        sum-error (r/add outer-error (r/mul df inner-error))
        triangle (t/app (rc "abs_add_lt") outer-error (r/mul df inner-error) bound bound outer-bound inner-scaled)
        sum-factor (ring "factor_sum" e2 ah)
        half-factor (t/app (rc "mul_congr_fst") ah (r/add e2 e2) eps (t/app (rc "half_add_half") eps))
        target-bound (r/mul eps ah)
        final-bound (t/app (k/const "Eq.trans" u) R (r/add bound bound) (r/mul (r/add e2 e2) ah)
                      target-bound sum-factor half-factor)
        hs (t/transport-at R u (t/lambda [[z R]] (r/lt (r/abs sum-error) z))
             (r/add bound bound) target-bound final-bound triangle)
        composite (t/lambda [[z R]] (t/app f (t/app g z)))
        final-error (remainder composite (r/mul df dg) x y)]
    (t/transport-at R u (t/lambda [[z R]] (r/lt (r/abs z) target-bound))
      sum-error final-error
      (ring "chain_error" (r/sub (t/app f gy) (t/app f gx)) (r/sub gy gx) df dg h) hs)))

(defn- install-chain [ctx]
  (decl ctx :thm "comp"
    (t/forall [[f FnR] [g FnR] [df R] [dg R] [x R]]
      (t/arrow (has-deriv-at f df (t/app g x))
        (t/arrow (has-deriv-at g dg x)
          (has-deriv-at (t/lambda [[y R]] (t/app f (t/app g y))) (r/mul df dg) x))))
    (t/lambda [[f FnR] [g FnR] [df R] [dg R] [x R]
               [hf (has-deriv-at f df (t/app g x))] [hg (has-deriv-at g dg x)]]
      (let [composite (t/lambda [[y R]] (t/app f (t/app g y)))
            derivative (r/mul df dg)
            remainder-goal (t/app (c "RemainderBound") composite derivative x)]
        (t/app (k/const "Iff.mpr") (has-deriv-at composite derivative x) remainder-goal
          (t/app (c "remainder_iff") composite derivative x)
          (t/lambda [[eps R] [he (pos eps)]]
            (let [gx (t/app g x) e2 (r/mul r/half eps)
                  he2 (t/app (rc "half_pos") eps he)
                  A (r/add (r/abs dg) r/one) B (r/add (r/abs df) r/one)
                  ea (r/mul (r/inv A) e2) eb (r/mul (r/inv B) e2)
                  hea (t/app (rc "mul_pos") (r/inv A) e2
                        (t/app (rc "inv_pos") A (t/app (rc "abs_add_one_pos") dg)) he2)
                  heb (t/app (rc "mul_pos") (r/inv B) e2
                        (t/app (rc "inv_pos") B (t/app (rc "abs_add_one_pos") df)) he2)
                  goal (t/exists' R (residual-predicate composite derivative x eps))]
              (t/with-cont
                [[do hdo hall-o] (residual-elim f df gx ea goal (t/app (residual-proof f df gx hf) ea hea))
                 [di hdi hall-i] (residual-elim g dg x eb goal (t/app (residual-proof g dg x hg) eb heb))
                 [ds hds hall-s] (near-elim (slope g x) x dg r/one goal (t/app hg r/one (rc "zero_lt_one")))
                 [dc hdc hall-c] (continuous-elim g x do goal (t/app (c "continuousAt") g dg x hg do hdo))
                 [dm hdm hmc hmi] (smaller-elim dc di hdc hdi goal)
                 [delta hd hdm' hds'] (smaller-elim dm ds hdm hds goal)]
                (t/exists-intro R (residual-predicate composite derivative x eps) delta
                  (t/and-intro (pos delta) (residual-body composite derivative x eps delta) hd
                    (t/lambda [[y R] [hy0 (pos (distance y x))] [hy (r/lt (distance y x) delta)]]
                      (let [dd (distance y x)
                            hm (t/app (rc "lt_trans") dd delta dm hy hdm')
                            hi (t/app (rc "lt_trans") dd dm di hm hmi)
                            hc (t/app (rc "lt_trans") dd dm dc hm hmc)
                            hs (t/app (rc "lt_trans") dd delta ds hy hds')]
                        (chain-estimate f g df dg x y eps he hy0 do hall-o
                          (t/app hall-i y hy0 hi) (t/app hall-s y hy0 hs) (t/app hall-c y hc))))))))))))))

(defn install
  "Pure. Declares this namespace's checked derivative laws into `ctx`."
  [ctx]
  (-> ctx
      install-limit-tools
      install-elementary
      install-product
      install-scaling
      install-remainder
      install-chain))

(defn install!
  "Installs analytic difference-quotient derivatives and the checked rules."
  []
  (locking k/install-lock
    (r/install!)
    (install-algebra!)
    (k/commit! install))
  :installed)
