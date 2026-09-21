#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.algebra-test
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [ansatz.kernel.expr :as e]
            [ansatz.kernel.level :as level]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.algebra :as alg]
            [emmy.ansatz.analysis.kernel :as t]
            [emmy.ansatz.analysis.order :as o]
            [emmy.ansatz.core :as k]))

(defn- verifies?
  "True if the kernel accepts `p` as a proof of its own statement, closed over
  `vars`."
  [vars p]
  (let [{:keys [statement proof]} (k/close vars p)]
    (env/verifies? (k/env) statement proof)))

(defn- pow [b n]
  (reduce k/mul (repeat n b)))

(deftest prove-eq-test
  (k/ensure-init!)
  (let [vars (k/fresh-vars '[x h])
        {x 'x h 'h} (into {} vars)
        x+h (k/add x h)]
    (testing "true identities produce kernel-checked proofs"
      (doseq [[lhs rhs] [[(k/mul x+h x+h)
                          (k/add (k/mul x x) (k/add (k/mul (k/lit 2) (k/mul x h)) (k/mul h h)))]
                         [(k/sub (k/mul x x) (k/mul h h))
                          (k/mul (k/add x h) (k/sub x h))]
                         [(k/neg (k/mul (k/lit -3) x))
                          (k/mul x (k/lit 3))]
                         [(k/add x (k/neg x)) k/zero]
                         [(pow x+h 4)
                          (reduce k/add [(pow x 4)
                                         (k/mul (k/lit 4) (k/mul (pow x 3) h))
                                         (k/mul (k/lit 6) (k/mul (pow x 2) (pow h 2)))
                                         (k/mul (k/lit 4) (k/mul x (pow h 3)))
                                         (pow h 4)])]]]
        (is (verifies? vars (alg/prove-eq lhs rhs))
            (k/->string lhs))))

    (testing "false identities are rejected"
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"not equal as polynomials"
                            (alg/prove-eq (k/mul x+h x+h)
                                          (k/add (k/mul x x) (k/mul h h))))))

    (testing "the kernel, not the normalizer, is the arbiter"
      (let [p (alg/prove-eq (k/mul x+h x+h)
                            (k/add (k/mul x x) (k/add (k/mul (k/lit 2) (k/mul x h)) (k/mul h h))))
            forged (assoc p :rhs (k/add (k/mul x x) (k/mul h h)))]
        (is (not (verifies? vars forged)))))))

(deftest int-ring-tactic-test
  (k/ensure-init!)
  (alg/install!)
  (testing "closes a ring identity over opaque atoms"
    (is (nil? (k/quietly
               (a/prove-theorem (gensym "int_ring_test")
                                '[x :- Int y :- Int]
                                '(= Int (Int.mul (Int.sub x y) (Int.add x y))
                                    (Int.sub (Int.mul x x) (Int.mul y y)))
                                '[(int_ring)])))))

  (testing "rewrites with hypotheses before normalizing"
    (is (nil? (k/quietly
               (a/prove-theorem (gensym "int_ring_test")
                                '[x :- Int y :- Int hxy :- (= Int x (Int.add y 1))]
                                '(= Int (Int.mul x x)
                                    (Int.add (Int.add (Int.mul y y) (Int.mul 2 y)) 1))
                                '[(int_ring [hxy])])))))

  (testing "fails on non-identities"
    (is (thrown? Exception
                 (k/quietly
                  (a/prove-theorem (gensym "int_ring_test")
                                   '[x :- Int]
                                   '(= Int (Int.mul x x) (Int.add x x))
                                   '[(int_ring)]))))))

(defn- bind-all
  "Wraps `body` in `binder` (e/forall' or e/lam) over `[name fvar type]`,
  outermost first."
  [binder binders body]
  (reduce (fn [acc [nm fv type]] (binder nm type (e/abstract1 acc (e/fvar-id fv)) :default))
          body
          (reverse binders)))

(deftest linear-combination-test
  (k/ensure-init!)
  (let [[[_ a] [_ b] [_ c] [_ d] [_ h1] [_ h2]] (k/fresh-vars '[a b c d h1 h2])
        binders [["a" a k/int-type] ["b" b k/int-type] ["c" c k/int-type]
                 ["d" d k/int-type] ["h1" h1 (k/eq a b)] ["h2" h2 (k/eq c d)]]
        hyp1 {:lhs a :rhs b :term h1}
        hyp2 {:lhs c :rhs d :term h2}
        lhs (k/add a (k/mul (k/lit 2) c))
        rhs (k/add b (k/mul (k/lit 2) d))]
    (testing "a + 2c = b + 2d follows from a = b and c = d"
      (let [p (alg/linear-combination lhs rhs [[k/one hyp1] [(k/lit 2) hyp2]])]
        (is (env/verifies? (k/env)
                           (bind-all e/forall' binders (k/eq lhs rhs))
                           (bind-all e/lam binders (:term p))))))
    (testing "wrong coefficients are rejected"
      (is (thrown? clojure.lang.ExceptionInfo
                   (alg/linear-combination lhs rhs [[k/one hyp1] [k/one hyp2]]))))))

(deftest context-arities-agree-with-the-global-forms
  (let [ctx (k/base-ctx)
        {x 'x h 'h} (into {} (k/fresh-vars '[x h]))
        lhs (k/mul (k/add x h) (k/add x h))
        rhs (k/add (k/mul x x) (k/add (k/mul (k/lit 2) (k/mul x h)) (k/mul h h)))]
    (testing "prove-eq"
      (is (= (:rhs (alg/prove-eq lhs rhs)) (:rhs (alg/prove-eq ctx lhs rhs)))))
    (testing "normalize-terms"
      (is (= (map first (alg/normalize-terms [lhs rhs]))
             (map first (alg/normalize-terms ctx [lhs rhs])))))
    (testing "linear-combination"
      (let [h1 {:lhs x :rhs h :term (:term (k/refl x))}
            p (alg/linear-combination ctx x h [[k/one h1]])]
        (is (= [x h] [(:lhs p) (:rhs p)]))))))

(deftest lemmas-are-read-from-the-given-environment
  (let [base (k/base-ctx)
        nat (k/const "Nat")
        u (level/succ level/zero)
        ;; Test.Lemma.refl : ∀ n : Nat, n = n, declared in one context only
        extended (t/declare-constant
                  base :thm "Test.Lemma.refl"
                  (t/forall [[n nat]] (k/eq-at nat u n n))
                  (t/lambda [[n nat]] (t/app (k/const "Eq.refl" u) nat n)))
        n (k/lit 3)]
    (testing "Init lemmas are instantiated at the given arguments"
      (is (= [(k/add n k/zero) n]
             ((juxt :lhs :rhs) (k/lemma-in base "Int.add_zero" n)))))
    (testing "a lemma declared in one context is invisible to another"
      (is (= [n n] ((juxt :lhs :rhs) (k/lemma-in extended "Test.Lemma.refl" n))))
      (is (thrown-with-msg? clojure.lang.ExceptionInfo #"Unknown lemma Test.Lemma.refl"
                            (k/lemma-in base "Test.Lemma.refl" n))))))

(deftest prove-law-runs-against-a-context
  (let [ctx (k/base-ctx)
        lt-one (fn [x] (o/lt k/zero x))
        goal (t/forall [[x k/int-type] [_h (lt-one x)]] (o/le k/one x))
        false-goal (t/forall [[x k/int-type] [_h (o/le k/zero x)]] (o/lt k/zero x))]
    (testing "omega closes a linear goal and the kernel accepts the result"
      (let [[statement proof] (k/prove-law ctx ["x" "h"] goal '[(omega)])]
        (is (= goal statement))
        (is (k/verifies? ctx statement proof))))
    (testing "an unprovable goal fails loudly"
      (is (thrown? Exception (k/prove-law ctx ["x" "h"] false-goal '[(omega)]))))))
