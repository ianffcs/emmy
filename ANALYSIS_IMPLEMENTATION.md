# Independent analysis in Emmy / Ansatz

This work uses Ansatz 0.2.114's bundled Init, not the Mathlib store.
It is **not yet a complete real analysis library**. The constructed real field,
completeness, limits, and epsilon-ball topology are implemented. Analytic
derivatives remain the next milestone (M5).

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
  `Int.mul_ediv_cancel`. The rational quotient field is implemented separately
  by `analysis.qfield` (M1).
- `algebra/linear-combination`: proves `lhs = rhs` from equational hypotheses
  (`lhs - rhs = Σ cᵢ·(lᵢ - rᵢ)` by `int_ring`), as Lean's `linear_combination`.
- `analysis.topology`: open-set spaces (empty/universal sets, finite binary
  intersections, arbitrary unions), inverse-image continuity, and checked
  continuity proofs for identity and composition.
- `analysis.real` (provisional, superseded by `analysis.reals`): integer/natural
  rational representatives `n/(d+1)`, exact
  rational distance bounds, proof-carrying Cauchy sequences, convergence-to-zero
  relation, and their quotient carrier. Checked `within_self`, `constant_cauchy`
  and quotient `sound` theorems. Constant rational sequences map into the carrier;
  injectivity of that map is not yet proved.

All new kernel declarations are definitions or theorems, checked with
`env/check-constant`. The bundled Init environment is still loaded in Ansatz's
trust mode. It supplies the underlying integers, quotient primitives and logic;
this work does not claim to have rechecked that imported library. The current
Q/R and real-topology theorem tests audit transitive axiom dependencies against
`propext`, `Quot.sound`, and `Classical.choice`. Quotient existence alone does
not prove field properties; those are separate checked theorems in M1–M3.

## Required next proofs, in dependency order

1. ~~Representative equivalence and operation congruence; the rational quotient
   field with order~~ (done, M1).
2. ~~Cauchy equivalence and well-defined arithmetic on the quotient; ring laws,
   inverse, order, Archimedean property, density and completeness~~ (done,
   M2/M3: `R` is a complete ordered field).
3. ~~Real epsilon-ball/open-set topology, neighborhood limits, continuity of
   arithmetic, and equivalence with preimage continuity~~ (done, M4).
4. ~~Epsilon-delta `HasDerivAt`, uniqueness and constant/id/add/neg/mul/chain
   laws; polynomial real semantics, rational cast bridge and derivative
   correctness~~ (done, M5/M6).
5. Finite-dimensional derivatives and Euler–Lagrange physics interfaces.

No field, completeness, or `HasDerivAt` axioms are introduced to bypass these
obligations. The implemented reals live under `Emmy.Analysis.R`; the superseded
provisional construction lives under `Emmy.Analysis.RealConstruction`. Neither
namespace claims drop-in compatibility with Mathlib.

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

## ℚ as an ordered field (M1)

`analysis.qfield` defines `Emmy.Analysis.Q.Q := Quot Rational.Rep Rational.Equiv`.
Operations are lifted with `lift1`/`lift2` (respect proved by the
representative congruences), relations with `lift2-prop` (via `propext`).
Laws are genuine equalities, proved by `Quot.ind` and `Quot.sound` of a
cross-multiplied identity (`quot-law!`, `q-theorem!`).

- Commutative ring: `add_comm`, `add_assoc`, `zero_add`, `add_left_neg`,
  `mul_comm`, `mul_assoc`, `one_mul`, `left_distrib`.
- Field: `inv` (`⟨n,d⟩⁻¹ = ⟨n·d, n·n⟩`, `0⁻¹ = 0`) with `inv_congr_rep`,
  `mul_inv_cancel : p ≠ 0 → p · p⁻¹ = 1`, `zero_ne_one`.
- Order: `lt`, `le` with `lt_irrefl`, `le_refl`, `le_of_lt`, `lt_trans`,
  `le_trans`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `le_antisymm`,
  `lt_trichotomy`, `add_lt_add_left`, `add_le_add_left`, `mul_pos`,
  `mul_nonneg`, `ne_of_lt`, `zero_lt_one`.
- `abs` with `abs_nonneg`, `abs_mul`, `abs_triangle`; `archimedean`
  (`∃ m : Int, p < ofInt m`); `half` with `half_pos`, `half_add_half`.

`by-omega` now ring-normalizes both sides of every relation first (shared atom
order), and respells literal coefficients as repeated sums, since Ansatz's
`omega` accepts no multiplication by literals.

## Cauchy reals (M2)

`analysis.reals` builds `Emmy.Analysis.R.R := Quot CSeq Equiv` on `Q`:

- `Cauchy s := ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → |s m − s n| < ε`,
  `CSeq := {s : Nat → Q // Cauchy s}`, and
  `Equiv s t := ∀ ε > 0, ∃ N, ∀ n, N ≤ n → |s n − t n| < ε`, with
  `equiv_refl`, `equiv_symm`, `equiv_trans`.
- `ofQ` through constant sequences (`const_cauchy`); `zero`, `one`.
- `bounded : Cauchy f → ∃ B, 0 < B ∧ ∀ n, |f n| < B`, via the finite bound
  `bounded_below` (by `Nat.rec`) and the Cauchy tail at ε = 1.
- Pointwise `addSeq`, `negSeq`, `mulSeq` with `add_cauchy`, `neg_cauchy`,
  `mul_cauchy` and the congruences `add_congr`, `neg_congr`, `mul_congr`; the
  operations `add`, `neg`, `sub`, `mul` on `R` are lifted by
  `lift1*`/`lift2*`. No choice is used for these.
- ε-N proofs split ε with `Q.half` and combine thresholds as `N₁ + N₂`. For
  products, `|a·c − b·d| ≤ |a|·|c − d| + |d|·|a − b|` (`Q.dist_mul_le`) with
  tolerances `B⁻¹·(ε/2)` (`Q.inv_pos`, `Q.mul_inv_mul`).

Ring laws on `R` (start of M3) are genuine equalities: `equiv_of_eq` turns a
pointwise `Q` law into `Equiv`, and `Quot.sound` gives `add_comm`, `add_assoc`,
`zero_add`, `add_left_neg`, `sub_self`, `mul_comm`, `mul_assoc`, `one_mul`,
`left_distrib`; `ofQ` is a ring homomorphism (`ofQ_add`, `ofQ_mul`, `ofQ_neg`).

Order on `R` (M3): `Pos s` says `s` is eventually bounded below by a positive
rational. It respects `Equiv` (`pos_congr`, by `Q.close_lower`: `ε < a` and
`|a − b| < ε/2` give `ε/2 < b`), so `propext` lifts it to `Positive : R → Prop`,
with `x < y := Positive (y − x)` and `x ≤ y := x < y ∨ x = y`. Proved:
`positive_add`, `not_positive_zero`, `lt_irrefl`, `lt_trans`, `add_lt_add_left`,
`le_refl`, `le_of_lt`, and the order embedding `ofQ_lt` / `lt_ofQ`.

Apartness and trichotomy (M3): `apart_of_ne` shows that a Cauchy sequence not
equivalent to zero is eventually bounded away from zero, by `Classical.byCases`
on that bound — the one classical step of the construction. Such a sequence
keeps a fixed sign past the Cauchy threshold (`pos_or_neg_of_apart`), which
gives `lt_trichotomy : x < y ∨ x = y ∨ y < x` on `R`, with
`eq_of_sub_eq_zero`.

`R.ofInt` and `archimedean : ∀ x, ∃ m : Int, x < ofInt m` follow from
boundedness of Cauchy sequences plus `Q.archimedean`.

The inverse (M3): `cinv` inverts a Cauchy sequence pointwise when it is apart
from zero (`Classical.propDecidable` decides which branch) and is zero
otherwise. Past the apartness threshold the estimate
`|a⁻¹ − b⁻¹| = |a⁻¹|·(|b⁻¹|·|b − a|)` (`Q.dist_inv_lt`, from `Q.inv_sub_inv`
and `Q.abs_inv_lt`) makes the inverted sequence Cauchy (`inv_cauchy`) and
respects equivalence (`inv_congr`, with `apart_congr`). This gives `R.inv` and
`mul_inv_cancel : x ≠ 0 → x · x⁻¹ = 1`, so `R` is a field. New `Q` inverse
lemmas: `inv_mul_cancel`, `inv_eq_of_mul_eq_one`, `inv_zero`, `abs_inv`,
`inv_lt_inv_of_lt`, `inv_mul_mul`, `abs_pos_of_ne_zero`, `abs_of_neg`.

Density and completeness (M3, complete): `dense : x < y → ∃ p : Q, x < ofQ p ∧
ofQ p < y`. `R.abs` is the pointwise absolute value (Cauchy by
`Q.abs_sub_abs_le`), with `dist_triangle_lt : |x − y| < a → |y − z| < b →
|x − z| < a + b`. `approx` puts a rational within any positive rational of any
real, so `Classical.choose` picks `g n` within `small n = (n+1)⁻¹` of `X n`;
`approx_cauchy` shows `g` is Cauchy and `complete : CauchyR X → ∃ L, TendsTo X L`
takes `L` to be its class. `Q.small` is positive, decreasing and eventually
below every positive rational (`small_lt`, from the Nat-indexed Archimedean
property `archimedean_nat` via `Int.le_natAbs`).

## Limits and continuity (M4)

`TendsToAt f x L := ∀ ε > 0, ∃ δ > 0, ∀ y, 0 < |y − x| → |y − x| < δ →
|f y − L| < ε` (the punctured ε-δ limit), with `ContinuousAt` in its
unpunctured form and `Continuous f := ∀ x, ContinuousAt f x`. Proved:
`tendsto_const`, `tendsto_id`, `tendsto_add`, `tendsto_neg`, `tendsto_mul`
(through `f y·g y − L·M = (f y − L)·g y + L·(g y − M)`, with `|g y|` bounded by
`|M| + 1` and tolerances `(|M|+1)⁻¹·(ε/2)`), `tendsto_unique` (two limits would
put `|L − M|` below itself, using `y = x + δ/2` as a nearby point), and
`continuousAt_of_tendsto`, `continuous_const`, `continuous_id`.

This rests on an order toolkit for `R`: the bridges `Pos_of_lt_zero` /
`lt_zero_of_Pos` (absorbing the `− 0` in `0 < x`), `abs_pos_of_ne`,
`abs_of_pos`, `mul_pos`, `inv_pos` (`1/B` bounds the inverse from below past
the Cauchy threshold), halving (`half_pos`, `half_lt_self`, `half_add_half`),
the strict estimates `dist_add_lt`, `abs_add_lt`, `abs_mul_lt`, `abs_lt_add`,
and `exists_pos_lt_both` standing in for a minimum. Each strict `R` inequality
is proved pointwise from a `Q` "gap" lemma (`triangle_gap`, `mul_gap`,
`abs_gap`).

Supporting `Q` lemmas: metric (`sub_self`, `abs_sub_comm`, `dist_triangle`,
`dist_add_le`, `dist_neg`, `add_lt_add`, `half_pos_of_pos`) and multiplicative
order (`mul_lt_mul_of_pos_left`, `mul_le_mul_of_nonneg_left`,
`mul_lt_of_lt_of_lt`, `abs_le_add_dist`, `le_add_of_nonneg_*`,
`lt_add_of_pos_*`).

### Epsilon-ball topology and continuity bridge

`emmy.ansatz.analysis.real-topology/install!` installs the real library and the
generic topology library, then declares `Emmy.Analysis.RealTopology.*`:

- `Ball x ε := {y | |y − x| < ε}`.
- `IsOpen U := ∀ x ∈ U, ∃ δ > 0, ∀ y, |y − x| < δ → y ∈ U`.
- `space : Topology.Space R`, with checked empty/universal, intersection and
  arbitrary-union axioms (`isOpen_empty`, `isOpen_univ`, `isOpen_inter`,
  `isOpen_sUnion`).
- `isOpen_ball` for every radius (including nonpositive radii), and
  `mem_ball_self` for positive radii.
- `continuous_iff : ∀ f, R.Continuous f ↔
  Topology.Continuous R R space space f`.

Intersections use `exists_pos_lt_both`. Ball openness uses rational density to
choose `b` strictly between `|x − center|` and the radius, then takes the local
radius `ε − b`. The reverse continuity bridge applies preimage openness to a
ball centered at `f x`; the forward bridge composes local epsilon-delta bounds.
The proof tests check complete statements, reject mismatched conclusions, and
audit dependencies against `propext`, `Quot.sound`, and `Classical.choice` only.

### Continuation combinator

`kernel/with-cont` flattens continuation-last proof eliminators:

```clojure
(t/with-cont [[d1 hd1 hall1] (near-elim f x L eps goal hf)
              [d2 hd2 hall2] (near-elim g x M eps goal hg)
              [d hd hda hdb] (pick-min d1 d2 hd1 hd2 goal)]
  (finish d hd hall1 hall2 hda hdb))
```

This is syntax for nested ordinary `fn` continuations, not a new tactic or proof
rule. The sum-limit proof and the real topology proofs use it. Scope, evaluation
order, malformed input, kernel verification, and lint bindings are covered by
tests and the associated clj-kondo hook.

## Analytic derivatives (M5) and the polynomial bridge (M6)

`analysis.derivative` defines the difference quotient `slope f x y` and
`HasDerivAt f d x := TendsToAt (slope f x) x d`, the punctured epsilon-delta
derivative. Proved: `unique`, `const`, `id`, `add`, `neg`, `mul` and `comp`
(the chain rule), plus `continuousAt` (differentiable implies continuous) and
the `RemainderBound` form `remainder_iff`, which converts between the
difference-quotient and first-order-residual statements — the residual form is
what the product and chain estimates use.

Ring identities in these proofs come from `reals/ring-identity!`, a function
that takes symbolic `+ * - 0 1` forms and installs the matching `Q` and `R`
laws by reduction to an integer ring identity; it is a proof builder, not a
trusted oracle (a false identity is rejected, and the tests check that).

`analysis.polynomial` gives `Emmy.PolyExpr` real semantics and proves
`deriv_hasDerivAt`: for every closed `PolyExpr`, the syntactic `deriv` computes
an analytic derivative of the function it denotes. That is the bridge from the
verified symbolic calculus to the epsilon-delta derivative on `R`.

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
