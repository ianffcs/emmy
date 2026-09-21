#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.real-topology
  "The epsilon-ball topology of the constructed reals and its continuity bridge.
  All definitions and proofs are checked by Ansatz; no Mathlib store is used."
  (:require [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.analysis.topology :as top]
            [emmy.ansatz.core :as k]))

(def ^:private u (level/succ level/zero))
(def ^:private prefix "Emmy.Analysis.RealTopology.")
(defn- c [s] (k/const (str prefix s)))
(defn- rc [s] (k/const (str "Emmy.Analysis.R." s)))
(def ^:private R r/R)
(def ^:private SetR (t/predicate R))
(def ^:private FnR (t/arrow R R))
(defn- pos [x] (r/lt r/zero x))
(defn- dist [x y] (r/abs (r/sub x y)))
(defn ball
  "The open ball as a kernel predicate."
  [x eps]
  (t/app (c "Ball") x eps))

(defn is-open
  "The epsilon-ball open-set predicate."
  [s]
  (t/app (c "IsOpen") s))

(def real-space
  "The constructed real topology, after `install!`."
  (c "space"))

(defn- preimage [f s]
  (t/lambda [[x R]] (t/app s (t/app f x))))
(defn- local-body [s x d]
  (t/forall [[y R]] (t/arrow (r/lt (dist y x) d) (t/app s y))))
(defn- local-predicate [s x]
  (t/lambda [[d R]] (t/and' (pos d) (local-body s x d))))
(defn- local [s x] (t/exists' R (local-predicate s x)))
(defn- local-intro [s x d hd hall]
  (t/exists-intro R (local-predicate s x) d
                  (t/and-intro (pos d) (local-body s x d) hd hall)))
(defn- local-elim [s x goal h next-proof]
  (t/exists-elim R (local-predicate s x) goal h
    (t/lambda [[d R] [hd (t/and' (pos d) (local-body s x d))]]
      (next-proof d (t/and-left (pos d) (local-body s x d) hd)
                  (t/and-right (pos d) (local-body s x d) hd)))))
(defn- smaller-elim [a b ha hb goal next-proof]
  (let [bounds (fn [d] (t/and' (r/lt d a) (r/lt d b)))
        p (t/lambda [[d R]] (t/and' (pos d) (bounds d)))]
    (t/exists-elim R p goal (t/app (rc "exists_pos_lt_both") a b ha hb)
      (t/lambda [[d R] [hd (t/and' (pos d) (bounds d))]]
        (let [h (t/and-right (pos d) (bounds d) hd)]
          (next-proof d (t/and-left (pos d) (bounds d) hd)
                      (t/and-left (r/lt d a) (r/lt d b) h)
                      (t/and-right (r/lt d a) (r/lt d b) h)))))))
(defn- intersection [a b]
  (t/lambda [[x R]] (t/and' (t/app a x) (t/app b x))))
(defn- union [family]
  (t/lambda [[x R]]
    (t/exists' SetR (t/lambda [[s SetR]] (t/and' (t/app family s) (t/app s x))))))
(defn- declare! [kind label type value]
  (when-not (k/installed? (str prefix label))
    (t/install-declaration! kind (str prefix label) type value)))

(defn- install-space! []
  (let [empty-set (t/lam "x" R (fn [_] t/false-prop))
        full-set (t/lam "x" R (fn [_] (k/const "True")))]
    (declare! :def "Ball" (t/arrow R (t/arrow R SetR))
      (t/lambda [[x R] [eps R] [y R]] (r/lt (dist y x) eps)))
    (declare! :def "IsOpen" (t/predicate SetR)
      (t/lambda [[s SetR]]
        (t/forall [[x R]] (t/arrow (t/app s x) (local s x)))))
    (declare! :thm "isOpen_empty" (is-open empty-set)
      (t/lambda [[x R] [h t/false-prop]] (t/false-elim (local empty-set x) h)))
    (declare! :thm "isOpen_univ" (is-open full-set)
      (t/lambda [[x R] [_hx (k/const "True")]]
        (local-intro full-set x r/one (rc "zero_lt_one")
          (t/lambda [[y R] [_hy (r/lt (dist y x) r/one)]] (k/const "True.intro")))))
    (declare! :thm "isOpen_inter"
      (t/forall [[a SetR] [b SetR]]
        (t/arrow (is-open a) (t/arrow (is-open b) (is-open (intersection a b)))))
      (t/lambda [[a SetR] [b SetR] [ha (is-open a)] [hb (is-open b)]
                 [x R] [hx (t/and' (t/app a x) (t/app b x))]]
        (let [s (intersection a b) goal (local s x)]
          (t/with-cont
            [[da hda hall-a] (local-elim a x goal (t/app ha x (t/and-left (t/app a x) (t/app b x) hx)))
             [db hdb hall-b] (local-elim b x goal (t/app hb x (t/and-right (t/app a x) (t/app b x) hx)))
             [d hd hda' hdb'] (smaller-elim da db hda hdb goal)]
            (local-intro s x d hd
              (t/lambda [[y R] [hy (r/lt (dist y x) d)]]
                (t/and-intro (t/app a y) (t/app b y)
                  (t/app hall-a y (t/app (rc "lt_trans") (dist y x) d da hy hda'))
                  (t/app hall-b y (t/app (rc "lt_trans") (dist y x) d db hy hdb')))))))))
    (declare! :thm "isOpen_sUnion"
      (t/forall [[family (t/predicate SetR)]]
        (t/arrow (t/forall [[s SetR]] (t/arrow (t/app family s) (is-open s)))
                 (is-open (union family))))
      (t/lambda [[family (t/predicate SetR)]
                 [hf (t/forall [[s SetR]] (t/arrow (t/app family s) (is-open s)))]
                 [x R] [hx (t/app (union family) x)]]
        (let [s-union (union family) goal (local s-union x)
              p (t/lambda [[s SetR]] (t/and' (t/app family s) (t/app s x)))]
          (t/exists-elim SetR p goal hx
            (t/lambda [[s SetR] [hs (t/and' (t/app family s) (t/app s x))]]
              (let [member (t/and-left (t/app family s) (t/app s x) hs)
                    contains-x (t/and-right (t/app family s) (t/app s x) hs)]
                (t/with-cont [[d hd hall] (local-elim s x goal (t/app hf s member x contains-x))]
                  (local-intro s-union x d hd
                    (t/lambda [[y R] [hy (r/lt (dist y x) d)]]
                      (t/exists-intro SetR
                        (t/lambda [[v SetR]] (t/and' (t/app family v) (t/app v y))) s
                        (t/and-intro (t/app family s) (t/app s y) member (t/app hall y hy))))))))))))
    (declare! :def "space" (top/space R)
      (top/space-intro R (c "IsOpen") (c "isOpen_empty") (c "isOpen_univ")
                       (c "isOpen_inter") (c "isOpen_sUnion")))))

(defn- install-balls! []
  (declare! :thm "mem_ball_self"
    (t/forall [[x R] [eps R]] (t/arrow (pos eps) (t/app (ball x eps) x)))
    (t/lambda [[x R] [eps R] [he (pos eps)]]
      (t/transport-at R u (t/lambda [[z R]] (r/lt z eps)) r/zero (dist x x)
        (t/app (k/const "Eq.symm" u) R (dist x x) r/zero (t/app (rc "abs_sub_self") x)) he)))
  (declare! :thm "isOpen_ball"
    (t/forall [[center R] [eps R]] (is-open (ball center eps)))
    (t/lambda [[center R] [eps R] [x R] [hx (t/app (ball center eps) x)]]
      (let [s (ball center eps) goal (local s x)
            p (t/lambda [[q r/Q]]
                (t/and' (r/lt (dist x center) (r/of-q q)) (r/lt (r/of-q q) eps)))]
        (t/exists-elim r/Q p goal (t/app (rc "dense") (dist x center) eps hx)
          (t/lambda [[q r/Q] [hq (t/app p q)]]
            (let [b (r/of-q q) delta (r/sub eps b)
                  hxb (t/and-left (r/lt (dist x center) b) (r/lt b eps) hq)
                  hbe (t/and-right (r/lt (dist x center) b) (r/lt b eps) hq)
                  hd (t/app (rc "lt_zero_of_positive") delta hbe)]
              (local-intro s x delta hd
                (t/lambda [[y R] [hy (r/lt (dist y x) delta)]]
                  (t/transport-at R u (t/lambda [[z R]] (r/lt (dist y center) z))
                    (r/add delta b) eps (t/app (rc "sub_add_cancel") eps b)
                    (t/app (rc "dist_triangle_lt") y x center delta b hy hxb)))))))))))

(defn- install-bridge! []
  (let [analytic #(t/app (rc "Continuous") %)
        topological #(top/continuous R R real-space real-space %)]
    (declare! :thm "continuous_iff"
      (t/forall [[f FnR]] (t/iff (analytic f) (topological f)))
      (t/lambda [[f FnR]]
        (t/iff-intro (analytic f) (topological f)
          (t/lambda [[hf (analytic f)] [s SetR] [hs (is-open s)]
                     [x R] [hx (t/app s (t/app f x))]]
            (let [goal (local (preimage f s) x) fx (t/app f x)]
              (t/with-cont [[eps he hall-s] (local-elim s fx goal (t/app hs fx hx))
                            [d hd hall-f] (local-elim (preimage f (ball fx eps)) x goal
                                           (t/app hf x eps he))]
                (local-intro (preimage f s) x d hd
                  (t/lambda [[y R] [hy (r/lt (dist y x) d)]]
                    (t/app hall-s (t/app f y) (t/app hall-f y hy)))))))
          (t/lambda [[hf (topological f)] [x R] [eps R] [he (pos eps)]]
            (let [fx (t/app f x) s (ball fx eps)]
              (t/app hf s (t/app (c "isOpen_ball") fx eps) x
                     (t/app (c "mem_ball_self") fx eps he)))))))))

(defn install!
  "Installs real epsilon-ball opens, the topology, and the two-way continuity
  bridge. Idempotent; requires only the independent constructed real library."
  []
  (locking k/install-lock
    (r/install!)
    (top/install!)
    (install-space!)
    (install-balls!)
    (install-bridge!))
  :installed)
