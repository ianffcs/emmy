#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis.metric
  "Checked metric-space vocabulary for the Ansatz analysis library.

  `MetricSpace a` is a real structure — a distance function on `a` bundled
  with a proof it satisfies the four laws needed by the ε–δ development: self
  distance, symmetry, separation, and the strict triangle estimate. It's
  built the same way `topology.clj`'s `Space` is: `Subtype (Distance a)
  (metric-laws a)`, via `Subtype.mk`/`Subtype.val`/`Subtype.property`. The
  strict triangle form composes directly with the existing real ε–δ proofs.

  The real instance uses `abs (x - y)`. Its ε-ball topology is derived
  generically here (`induced-space`, needing no metric-law proof at all — any
  distance-shaped function's ε-balls satisfy the topology axioms) rather than
  hardcoded to `R`, so any future `MetricSpace a` instance gets its induced
  topology for free."
  (:require [ansatz.kernel.level :as level]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.reals :as r]
            [emmy.ansatz.analysis.topology :as topology]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.install :as registry]))

(def ^:private prefix "Emmy.Analysis.Metric.")
(def ^:private u (level/succ level/zero))
(def ^:private R r/R)
(def ^:private Prop t/prop)

(defn distance-type
  "The type of real-valued distances on a carrier `a`."
  [a]
  (t/>-> a a R))

(defn distance
  "Apply a metric distance function to two points."
  [d x y]
  (t/app d x y))

(defn- law-parts
  "The four metric-law propositions for `d : Distance a`, as a map, in the
  same nested order `metric-laws` conjoins them (self, (comm, (sep,
  triangle))). Factored out so `metric-laws` and the per-law bridges below
  build the exact same proposition terms."
  [a d]
  (let [dist #(distance d %1 %2)]
    {:self (t/forall [[x a]] (k/eq-at R u (dist x x) r/zero))
     :comm (t/forall [[x a] [y a]] (k/eq-at R u (dist x y) (dist y x)))
     :sep (t/forall [[x a] [y a]]
            (t/>-> (t/not' (k/eq-at a u x y))
                   (r/lt r/zero (dist x y))))
     :triangle (t/forall [[x a] [y a] [z a] [eps R] [delta R]]
                 (t/>-> (r/lt (dist x y) eps)
                        (r/lt (dist y z) delta)
                        (r/lt (dist x z) (r/add eps delta))))}))

(defn metric-laws
  "The proposition expressing the checked metric laws for `d : Dist a`."
  [a d]
  (let [{:keys [self comm sep triangle]} (law-parts a d)]
    (t/and' self (t/and' comm (t/and' sep triangle)))))

(defn- metric-predicate [a]
  (t/lam "d" (distance-type a) #(metric-laws a %)))

(defn metric-space
  "The type of metric structures on `a`: a distance function bundled with a
  proof it satisfies the metric laws. A `Type0`, not a `Prop` — the structure
  itself is data, not merely an existence claim."
  [a]
  (t/app (k/const "Subtype" u) (distance-type a) (metric-predicate a)))

(defn metric-space-intro
  "Constructs a `MetricSpace a` from a distance `d` and a proof of the metric
  laws for `d`. Mirrors `topology/space-intro`."
  [a d proof]
  (t/app (k/const "Subtype.mk" u) (distance-type a) (metric-predicate a) d proof))

(defn metric-space-dist
  "The distance function bundled in `M : MetricSpace a`."
  [a M]
  (t/app (k/const "Subtype.val" u) (distance-type a) (metric-predicate a) M))

(defn metric-space-proof
  "The proof that `metric-space-dist a M` satisfies the metric laws."
  [a M]
  (t/app (k/const "Subtype.property" u) (distance-type a) (metric-predicate a) M))

;; ## Bridges: named access to each metric law from a `MetricSpace` instance,
;; so callers never need to unpack `metric-space-proof`'s conjunction by hand.

(defn- law-proof-parts
  [a M]
  (let [d (metric-space-dist a M)
        {:keys [self comm sep triangle]} (law-parts a d)
        rest1 (t/and' comm (t/and' sep triangle))
        rest2 (t/and' sep triangle)
        proof (metric-space-proof a M)
        p-rest1 (t/and-right self rest1 proof)
        p-rest2 (t/and-right comm rest2 p-rest1)]
    {:self (t/and-left self rest1 proof)
     :comm (t/and-left comm rest2 p-rest1)
     :sep (t/and-left sep triangle p-rest2)
     :triangle (t/and-right sep triangle p-rest2)}))

(defn dist-self
  "Proof of `∀ x, dist x x = 0` for `M : MetricSpace a`."
  [a M] (:self (law-proof-parts a M)))

(defn dist-comm
  "Proof of `∀ x y, dist x y = dist y x` for `M : MetricSpace a`."
  [a M] (:comm (law-proof-parts a M)))

(defn dist-pos-of-ne
  "Proof of `∀ x y, x ≠ y → 0 < dist x y` for `M : MetricSpace a`."
  [a M] (:sep (law-proof-parts a M)))

(defn dist-triangle
  "Proof of the strict triangle estimate for `M : MetricSpace a`."
  [a M] (:triangle (law-proof-parts a M)))

;; ## Balls and the ε-ball open-set predicate

(defn ball
  "The open ball of radius `eps` around `center` for `d`."
  [a d center eps]
  (t/lam "y" a (fn [y] (r/lt (distance d y center) eps))))

(defn metric-is-open
  "The ε-ball definition of openness for a distance function."
  [a d set]
  (t/forall [[x a]]
    (t/>-> (t/app set x)
           (t/exists' R
             (t/lambda [[eps R]]
               (t/and' (r/lt r/zero eps)
                       (t/forall [[y a]]
                         (t/>-> (r/lt (distance d y x) eps)
                                (t/app set y)))))))))

;; ## The induced topology
;;
;; Generalizes `real-topology.clj`'s ε-ball construction from hardcoded
;; `(R, abs∘sub)` to any `(a, d)`. None of the four topology axioms below
;; need `d` to satisfy the metric laws — any distance-shaped function's
;; ε-balls form a valid topology — so `induced-space` takes a bare `d`, not a
;; `MetricSpace a`.

(defn- local-body [a d s x delta]
  (t/forall [[y a]] (t/arrow (r/lt (distance d y x) delta) (t/app s y))))
(defn- local-predicate [a d s x]
  (t/lambda [[delta R]] (t/and' (r/lt r/zero delta) (local-body a d s x delta))))
(defn- local [a d s x] (t/exists' R (local-predicate a d s x)))
(defn- local-intro [a d s x delta hd hall]
  (t/exists-intro R (local-predicate a d s x) delta
    (t/and-intro (r/lt r/zero delta) (local-body a d s x delta) hd hall)))
(defn- local-elim [a d s x goal h next-proof]
  (t/exists-elim R (local-predicate a d s x) goal h
    (t/lambda [[delta R] [hd (t/and' (r/lt r/zero delta) (local-body a d s x delta))]]
      (next-proof delta (t/and-left (r/lt r/zero delta) (local-body a d s x delta) hd)
                  (t/and-right (r/lt r/zero delta) (local-body a d s x delta) hd)))))
(defn- smaller-elim [p q hp hq goal next-proof]
  (let [bounds (fn [delta] (t/and' (r/lt delta p) (r/lt delta q)))
        pred (t/lambda [[delta R]] (t/and' (r/lt r/zero delta) (bounds delta)))]
    (t/exists-elim R pred goal (t/app (k/const "Emmy.Analysis.R.exists_pos_lt_both") p q hp hq)
      (t/lambda [[delta R] [hd (t/and' (r/lt r/zero delta) (bounds delta))]]
        (let [h (t/and-right (r/lt r/zero delta) (bounds delta) hd)]
          (next-proof delta (t/and-left (r/lt r/zero delta) (bounds delta) hd)
                      (t/and-left (r/lt delta p) (r/lt delta q) h)
                      (t/and-right (r/lt delta p) (r/lt delta q) h)))))))
(defn- intersection [a p q]
  (t/lambda [[x a]] (t/and' (t/app p x) (t/app q x))))
(defn- union [a family]
  (t/lambda [[x a]]
    (t/exists' (t/predicate a)
      (t/lambda [[v (t/predicate a)]] (t/and' (t/app family v) (t/app v x))))))

(defn- isOpen-empty-proof [a d]
  (let [empty-set (t/lam "x" a (fn [_] t/false-prop))]
    (t/lambda [[x a] [h t/false-prop]] (t/false-elim (local a d empty-set x) h))))

(defn- isOpen-univ-proof [a d]
  (let [full-set (t/lam "x" a (fn [_] (k/const "True")))]
    (t/lambda [[x a] [_hx (k/const "True")]]
      (local-intro a d full-set x r/one (k/const "Emmy.Analysis.R.zero_lt_one")
        (t/lambda [[y a] [_hy (r/lt (distance d y x) r/one)]] (k/const "True.intro"))))))

(defn- isOpen-inter-proof [a d]
  (t/lambda [[p (t/predicate a)] [q (t/predicate a)]
             [hp (metric-is-open a d p)] [hq (metric-is-open a d q)]
             [x a] [hx (t/and' (t/app p x) (t/app q x))]]
    (let [s (intersection a p q) goal (local a d s x)]
      (t/with-cont
        [[dp hdp hall-p] (local-elim a d p x goal (t/app hp x (t/and-left (t/app p x) (t/app q x) hx)))
         [dq hdq hall-q] (local-elim a d q x goal (t/app hq x (t/and-right (t/app p x) (t/app q x) hx)))
         [delta hd hdp' hdq'] (smaller-elim dp dq hdp hdq goal)]
        (local-intro a d s x delta hd
          (t/lambda [[y a] [hy (r/lt (distance d y x) delta)]]
            (t/and-intro (t/app p y) (t/app q y)
              (t/app hall-p y (t/app (k/const "Emmy.Analysis.R.lt_trans") (distance d y x) delta dp hy hdp'))
              (t/app hall-q y (t/app (k/const "Emmy.Analysis.R.lt_trans") (distance d y x) delta dq hy hdq')))))))))

(defn- isOpen-sUnion-proof [a d]
  (t/lambda [[family (t/predicate (t/predicate a))]
             [hf (t/forall [[s (t/predicate a)]] (t/arrow (t/app family s) (metric-is-open a d s)))]
             [x a] [hx (t/app (union a family) x)]]
    (let [s-union (union a family) goal (local a d s-union x)
          p (t/lambda [[s (t/predicate a)]] (t/and' (t/app family s) (t/app s x)))]
      (t/exists-elim (t/predicate a) p goal hx
        (t/lambda [[s (t/predicate a)] [hs (t/and' (t/app family s) (t/app s x))]]
          (let [member (t/and-left (t/app family s) (t/app s x) hs)
                contains-x (t/and-right (t/app family s) (t/app s x) hs)]
            (t/with-cont [[delta hd hall] (local-elim a d s x goal (t/app hf s member x contains-x))]
              (local-intro a d s-union x delta hd
                (t/lambda [[y a] [hy (r/lt (distance d y x) delta)]]
                  (t/exists-intro (t/predicate a)
                    (t/lambda [[v (t/predicate a)]] (t/and' (t/app family v) (t/app v y))) s
                    (t/and-intro (t/app family s) (t/app s y) member (t/app hall y hy))))))))))))

(defn induced-space
  "The `Space a` (from `topology.clj`) induced by the ε-ball topology of
  distance `d`. Needs no metric-law proof: openness-via-ε-balls satisfies the
  four topology axioms for any `d : Distance a`."
  [a d]
  (topology/space-intro a (t/lam "s" (t/predicate a) #(metric-is-open a d %))
                         (isOpen-empty-proof a d)
                         (isOpen-univ-proof a d)
                         (isOpen-inter-proof a d)
                         (isOpen-sUnion-proof a d)))

;; ## The constructed-real instance

(defn real-distance
  "The constructed-real distance `|x - y|`."
  [x y]
  (r/abs (r/sub x y)))

(def real-metric-distance
  "The real distance function as a kernel term."
  (t/lam "x" R (fn [x] (t/lam "y" R (fn [y] (real-distance x y))))))

(defn- eq-refl [type x]
  (t/app (k/const "Eq.refl" u) type x))

(defn- real-laws-proof []
  (let [d real-metric-distance
        dist #(distance d %1 %2)
        {:keys [self comm sep triangle]} (law-parts R d)
        rest1 (t/and' comm (t/and' sep triangle))]
    (t/and-intro self rest1
     (t/lambda [[x R]]
       (t/app (k/const "Eq.trans" u) R (dist x x) (r/abs (r/sub x x)) r/zero
              (eq-refl R (dist x x))
              (t/app (k/const "Emmy.Analysis.R.abs_sub_self") x)))
     (t/and-intro comm (t/and' sep triangle)
      (t/lambda [[x R] [y R]]
       (t/app (k/const "Emmy.Analysis.R.abs_sub_comm") x y))
      (t/and-intro sep triangle
       (t/lambda [[x R] [y R] [hne (t/not' (k/eq-at R u x y))]]
         (t/app (k/const "Emmy.Analysis.R.abs_pos_of_ne") x y hne))
       (t/lambda [[x R] [y R] [z R] [eps R] [delta R]
                  [hxy (r/lt (dist x y) eps)]
                  [hyz (r/lt (dist y z) delta)]]
         (t/app (k/const "Emmy.Analysis.R.dist_triangle_lt") x y z eps delta hxy hyz)))))))

(def real-metric-space
  "The constructed-real metric space: `real-metric-distance` bundled with its
  proof of the metric laws."
  (metric-space-intro R real-metric-distance (real-laws-proof)))

(def ^:private decl (t/declarer prefix))

(defn install
  "Pure. Declares checked metric definitions and the constructed-real
  instance and its induced topology into `ctx`."
  [ctx]
  (-> ctx
      (decl :def "Distance" (t/>-> t/type0 t/type0)
            (t/lam "A" t/type0 distance-type))
      (decl :def "MetricSpace" (t/>-> t/type0 t/type0)
            (t/lam "A" t/type0 metric-space))
      (decl :def "Ball"
            (t/forall [[a t/type0]]
              (t/>-> (distance-type a) a R (t/predicate a)))
            (t/lam "A" t/type0
                   (fn [a]
                     (t/lam "d" (distance-type a)
                            (fn [d]
                              (t/lam "center" a
                                     (fn [center]
                                       (t/lam "eps" R
                                              (fn [eps]
                                                (t/lam "y" a
                                                       (fn [y]
                                                         (r/lt (distance d y center) eps))))))))))))
      (decl :def "IsOpen"
            (t/forall [[a t/type0]]
              (t/>-> (distance-type a) (t/predicate a) Prop))
            (t/lam "A" t/type0
                   (fn [a]
                     (t/lam "d" (distance-type a)
                            (fn [d]
                              (t/lam "set" (t/predicate a)
                                     (fn [set] (metric-is-open a d set))))))))
      (decl :def "realDistance" (distance-type R) real-metric-distance)
      (decl :thm "realMetricLaws" (metric-laws R real-metric-distance) (real-laws-proof))
      (decl :def "realInstance" (metric-space R) real-metric-space)
      (decl :def "space" (topology/space R) (induced-space R real-metric-distance))))

(defn install!
  "Install checked metric definitions and the constructed-real instance."
  []
  (registry/install-through! 'emmy.ansatz.analysis.metric)
  :installed)
