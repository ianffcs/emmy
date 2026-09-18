# Independent analysis in Emmy / Ansatz

This work uses Ansatz 0.2.114's bundled Init, not the Mathlib store.
It is **not yet a complete real analysis library**. Constructed real field
operations, completeness and analytic derivatives remain required deliverables.

## Implemented and checked

- `analysis.kernel`: typed dependent binders and checked definition/theorem
  installation. Nil values and axiom installation are rejected.
- `analysis.rational`: exact normalized host representatives; kernel proofs of
  eight cross-multiplied representative ring identities. Kernel layer
  `Emmy.Analysis.Rational.*`: representatives `{p : Int × Int // 0 < p.2}` with
  `num`, `den`, `den_pos`, `add`, `mul`, `neg`; the relation
  `Equiv a b := num a * den b = num b * den a` with `equiv_refl`, `equiv_symm`,
  `equiv_trans`; and `add_congr`, `mul_congr`, `neg_congr`. Transitivity uses
  `int_mul_right_cancel` (`0 < d → a*d = b*d → a = b`), derived from Init's
  `Int.mul_ediv_cancel`. Normalization and the rational quotient field are not
  yet proved.
- `algebra/linear-combination`: proves `lhs = rhs` from equational hypotheses
  (`lhs - rhs = Σ cᵢ·(lᵢ - rᵢ)` by `int_ring`), as Lean's `linear_combination`.
- `analysis.topology`: open-set spaces (empty/universal sets, finite binary
  intersections, arbitrary unions), inverse-image continuity, and checked
  continuity proofs for identity and composition.
- `analysis.real`: integer/natural rational representatives `n/(d+1)`, exact
  rational distance bounds, proof-carrying Cauchy sequences, convergence-to-zero
  relation, and their quotient carrier. Checked `within_self`, `constant_cauchy`
  and quotient `sound` theorems. Constant rational sequences map into the carrier;
  injectivity of that map is not yet proved.

All new kernel declarations are definitions or theorems, checked with
`env/check-constant`. The bundled Init environment is still loaded in Ansatz's
trust mode. It supplies the underlying integers, quotient primitives and logic;
this work does not claim to have rechecked that imported library or completed
a transitive axiom audit. Quotient existence alone does not prove that the
carrier has the real field's mathematical properties.

## Required next proofs, in dependency order

1. ~~Representative equivalence and operation congruence~~ (done); the rational
   quotient `Quot Equiv` with lifted operations and its field laws (the
   representative identities above lift through `Quot.sound`); normalization
   correctness; order; executable/proof representation bridge.
2. Cauchy equivalence, well-defined arithmetic and inverse on the quotient;
   rational embedding, order, Archimedean property, density, and completeness.
3. Real metric/open-set topology, neighborhood limits, continuity of arithmetic.
4. Epsilon-delta `HasDerivAt`, uniqueness and constant/id/add/neg/mul/chain laws;
   polynomial real semantics, rational cast bridge and derivative correctness.
5. Finite-dimensional derivatives and Euler–Lagrange physics interfaces.

No `Real` complete ordered field, completeness axiom, or `HasDerivAt` axiom is
introduced to bypass these obligations. The provisional construction lives under
`Emmy.Analysis.RealConstruction`, rather than claiming compatibility with Mathlib.

## Proof infrastructure (M0)

- `analysis.kernel`: logic builders (`and-intro`, `or-elim`, `exists-intro`,
  `exists-elim`, `decidable-em`, `classical-em`, `transport`, `propext'`,
  quotient `quot-mk`/`quot-sound`/`quot-lift`/`quot-ind`) and the axiom audit
  `axioms-of`, which walks every constant a declaration depends on.
- `analysis.order`: `by-omega` proves a linear-arithmetic goal from hypotheses,
  abstracting non-linear subterms (products, `num a`, `abs x`) to variables and
  applying Ansatz's `omega` proof back to them; nonlinear facts are passed in as
  hypotheses. `rewrite-prop` rewrites a proposition along a ring identity.
- `Emmy.Analysis.Int.*`: `lt_trans`, `add_pos`, `add_nonneg`, `mul_nonneg`,
  `abs` (by `ite` on `Int.decLe`) with `abs_cases`, `abs_nonneg`, `le_abs`,
  `neg_le_abs`, `abs_neg`, `abs_triangle`, `abs_sub_comm`, `abs_lt`, `abs_mul`.
  Axioms: `propext`, plus `Quot.sound` and `Classical.choice` wherever Ansatz's
  `omega` proofs are used.

## Rational coefficients in the verified calculus

`Emmy.PolyExpr` has a `frac p q` constructor (`p/(q+1)`). Expressions are
interpreted as rationals: `num`/`den` with `den_pos`, packaged as
`value : … → Emmy.Analysis.Rational.Rep`. Checked theorems:

- `deriv_correct` in cross-multiplied Carathéodory form (no division in the
  kernel), with step lemmas `deriv_correct_add|mul|neg` proved by
  `linear-combination`;
- `simp_correct : Equiv (value (simp e)) (value e)`, by `equiv_trans` and the
  `Rational.*_congr` lemmas; smart-constructor lemmas by `int_ring_split`;
- per-rule soundness, `step_correct` and `simp_correct` for every rule set, in
  the same `Equiv` form.

The earlier host-side scaling (`{:numerator :denominator}`) is removed: rational
coefficients are no longer trusted glue. Fractions are not yet folded with each
other by `simp`; Emmy's simplifier does that downstream.

## API correction

The previous `physlib/has-deriv-at` map was not a proof. It is replaced by
`polynomial-derivative-report`, explicitly marked `:certified? false`.
`has-deriv-at?` is removed. `real-value` is renamed `approximate-value`.
It uses double arithmetic and has no certified approximation bound.

## Verification

Run the scoped suite with a regex (not a wildcard passed to `-n`):

```sh
clojure -M:test -m cognitect.test-runner -d test -r 'emmy\.ansatz\..*-test'
bb lint
```

Proof tests recheck full closed propositions and reject mismatched statements.
No Mathlib download is needed. Exact runtime representative tests include negative
denominators, zero, fractions and arithmetic beyond signed 64-bit range.
