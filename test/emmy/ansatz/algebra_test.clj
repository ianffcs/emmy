#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.algebra-test
  (:require [ansatz.core :as a]
            [ansatz.kernel.env :as env]
            [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.algebra :as alg]
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
