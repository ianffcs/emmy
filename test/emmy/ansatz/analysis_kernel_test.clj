#_"SPDX-License-Identifier: GPL-3.0"

(ns emmy.ansatz.analysis-kernel-test
  (:require [clojure.test :refer [deftest is]]
            [emmy.ansatz.analysis.kernel :as t]))

(deftest arrow-threading
  (is (= '(emmy.ansatz.analysis.kernel/arrow A B)
         (macroexpand '(emmy.ansatz.analysis.kernel/-> A (emmy.ansatz.analysis.kernel/arrow B)))))
  (is (= '(emmy.ansatz.analysis.kernel/arrow
           (emmy.ansatz.analysis.kernel/arrow A B) C)
         (macroexpand '(emmy.ansatz.analysis.kernel/-> A (emmy.ansatz.analysis.kernel/arrow B) (emmy.ansatz.analysis.kernel/arrow C)))))
  (is (= '(emmy.ansatz.analysis.kernel/arrow A B C)
         (macroexpand '(emmy.ansatz.analysis.kernel/-> A (emmy.ansatz.analysis.kernel/arrow B C)))))
  (is (= 'A (macroexpand '(emmy.ansatz.analysis.kernel/-> A))))
  (is (= '(emmy.ansatz.analysis.kernel/arrow A B C)
         (macroexpand '(emmy.ansatz.analysis.kernel/-> A (emmy.ansatz.analysis.kernel/arrow B C))))))

(deftest implication-chain
  (is (= '(emmy.ansatz.analysis.kernel/arrow A B)
         (macroexpand '(emmy.ansatz.analysis.kernel/>-> A B))))
  (is (= '(emmy.ansatz.analysis.kernel/arrow
           A (emmy.ansatz.analysis.kernel/arrow B C))
         (macroexpand '(emmy.ansatz.analysis.kernel/>-> A B C))))
  (is (= '(emmy.ansatz.analysis.kernel/arrow
           A (emmy.ansatz.analysis.kernel/arrow
              B (emmy.ansatz.analysis.kernel/arrow C D)))
         (macroexpand '(emmy.ansatz.analysis.kernel/>-> A B C D))))
  (is (thrown? clojure.lang.Compiler$CompilerException
                (macroexpand '(emmy.ansatz.analysis.kernel/>-> A))))
  (is (thrown? clojure.lang.Compiler$CompilerException
                (macroexpand '(emmy.ansatz.analysis.kernel/>->)))))
