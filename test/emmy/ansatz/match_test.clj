#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.match-test
  (:require [clojure.test :refer [deftest is testing]]
            [emmy.ansatz.core :as k]
            [emmy.ansatz.expression :as ax]
            [emmy.ansatz.match :as m]))

(defn- define-and-run
  "Defines `nm` through the front end and returns its compiled fn."
  [nm params ret body]
  (ax/install!)
  (ax/define! nm params ret body)
  (ax/compiled-fn (str nm)))

(deftest desugar-test
  (k/ensure-init!)
  (testing "one-level top-level matches pass through unchanged"
    (let [body '(match c [(Int.ofNat n) n] [(Int.negSucc n) n])]
      (is (= [['T.id '[c :- Int] 'Nat body]]
             (m/desugar 'T.id '[c :- Int] 'Nat body)))))

  (testing "nested matches are lifted into auxiliary definitions"
    (let [defs (m/desugar 'T.lifted '[c :- Int] 'Nat
                          '(match c [(Int.ofNat n) (match n [0 1] [_ 0])] [(Int.negSucc n) 0]))]
      (is (= ['T.lifted._match_0 'T.lifted] (mapv first defs)))
      (is (= '[n :- Nat] (second (first defs))))))

  (testing "non-exhaustive nested patterns are rejected"
    (is (thrown-with-msg? clojure.lang.ExceptionInfo #"non-exhaustive"
                          (m/desugar 'T.bad '[c :- Int] 'Nat
                                     '(match c [(Int.ofNat 0) 1]))))))

(deftest runtime-test
  (testing "nested literal patterns"
    (let [is-zero (define-and-run 'T.isZero '[c :- Int] 'Nat '(match c [(Int.ofNat 0) 1] [_ 0]))
          is-one  (define-and-run 'T.isOne '[c :- Int] 'Nat '(match c [(Int.ofNat 1) 1] [_ 0]))]
      (is (= [1 0 0 0] (mapv is-zero [0 1 -1 (bigint -100000000000000000000)])))
      (is (= [0 1 0 0] (mapv is-one [0 1 2 -1])))))

  (testing "literal and variable sub-patterns on the same constructor"
    (let [f (define-and-run 'T.mixed '[c :- Int] 'Nat
              '(match c [(Int.ofNat 0) 5] [(Int.ofNat n) n] [(Int.negSucc m) m]))]
      (is (= [5 3 0 1] (mapv f [0 3 -1 -2])))))

  (testing "a nested match on a pattern variable"
    (let [f (define-and-run 'T.nested '[c :- Int] 'Nat
              '(match c [(Int.ofNat n) (match n [0 1] [_ 0])] [(Int.negSucc n) 0]))]
      (is (= [1 0 0] (mapv f [0 3 -2])))))

  (testing "Int constructors are lowered to integers, not vectors"
    (let [f (define-and-run 'T.echo '[c :- Int] 'Int
              '(match c [(Int.ofNat n) (Int.ofNat n)] [(Int.negSucc n) (Int.negSucc n)]))]
      (is (= [0 7 -1 -8] (mapv f [0 7 -1 -8]))))))
