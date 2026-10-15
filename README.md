# Baker–Harman small remainders

A Lean 4 / Mathlib formalisation of the full unequal-weight Theorems 1 and 2 of:

> R. C. Baker and G. Harman, *Small remainder of a vector to suitable modulus*,
> Math. Z. 221 (1996), 59–71, [doi:10.1007/BF02622099](https://doi.org/10.1007/BF02622099).

Both original theorems are proved with their explicit rounded exponent. Stronger
versions retain the exponent quoted in Lemma 5 of Heyman–Shparlinski,
*On the greatest common divisor of shifted sets*, J. Number Theory 154 (2015),
63–73, [doi:10.1016/j.jnt.2015.02.012](https://doi.org/10.1016/j.jnt.2015.02.012).

The proof adapts the paper's analytic and lattice strategy. It uses Gaussian
Fourier detection and an induction with power slack to recover the original
logarithmic degrees. The equal-weight specialization and earlier lattice theorem
remain available with their existing statements.

## Main results

Import `BakerHarman.OriginalTheorem` for Theorem 1, `BakerHarman.TheoremTwo` for
both theorems, or `BakerHarman` for the entire library. Declarations live in the `BakerHarman` namespace.

- [`bakerHarman_theorem_one`](BakerHarman/OriginalTheorem.lean): for every positive
  dimension `n` and `K > 0`, there are constants `C₁ ≥ 1` and `C₂ > 0` such that,
  for natural `Q,R` with `C₁ ≤ Q ≤ R^c(K)`, any real vector `a` with Euclidean norm
  at most `R^K`, and positive tolerances satisfying
  `ψᵢ ≤ C₂⁻¹(log Q)⁻ⁿ` and `∏ ψᵢ = Q⁻¹`, there is a natural modulus
  `R ≤ r ≤ 2QR` with `distNearestInt (aᵢ/r) ≤ ψᵢ` for every coordinate.
  Here `c(K) = 1/(2^(k+1)-4)` and `k = ⌈1 + max(1,K)⌉`, as in equation (2.1).
  There is no additional hypothesis that `R` exceeds an independent threshold.
- [`bakerHarman_theorem_two`](BakerHarman/TheoremTwo.lean) gives the improved
  modulus bound for large weighted vectors. Under the same types of hypotheses,
  with constants depending only on `n,K`, assume additionally
  `maxᵢ |aᵢ|/ψᵢ ≥ C₂ RQ(log Q)ⁿ`. Then the modulus satisfies
  `R ≤ r ≤ C₃ RQ(log Q)ⁿ⁻¹ maxᵢ ψᵢ`, with all coordinate errors at most `ψᵢ`.
  The same `C₂` appears in the tolerance restriction and the large-vector
  hypothesis, matching equations (1.12)–(1.13). Arbitrary real coordinate signs
  and dimension one are included.
- [`bakerHarman_theorem_two_log`](BakerHarman/TheoremTwo.lean) gives Theorem 2
  with the stronger exponent `γ(K)` and real `Q,R`. The supporting
  `bakerHarman_large_weighted_vector` retains `log Q + 1`, separate thresholds,
  and only the tolerance restriction `ψᵢ ≤ 1`.
- [`bakerHarman_unequal_weights_log`](BakerHarman/OriginalTheorem.lean) gives the
  same logarithmic tolerance condition with the stronger exponent
  `γ(K) = 1/(2^(2 + max(1,K))-4)`. It permits real `Q,R` with `R ≥ 1`.
- [`bakerHarman_unequal_weights`](BakerHarman/UnequalWeights.lean) gives the
  intermediate form with tolerances bounded by `c/(log Q + 1)^n` and explicit
  thresholds for both `Q` and `R`. All real coordinate signs are allowed, and
  dimension one is included.
- [`bakerHarman_sharp_lattice_approximation`](BakerHarman/SharpDimensionInduction.lean)
  proves the supporting lattice theorem with input logarithmic degree `d` and
  output degree `d−1`, uniformly over real inner product spaces and full lattices.
  Its precise hypotheses are recorded in `PowerLatticeStatement`. It is valid for
  every positive power exponent strictly below `(26/25)γ(K)`, for `K ≥ 1`.
- [`bakerHarman_equal_weights`](BakerHarman/EqualWeights.lean) remains the original
  entry point for the shifted-sets application: for `n ≥ 2`, `K ≥ 1`, sufficiently
  large real `Q,R`, and `Q ≤ R^γ(K)`, it gives common tolerance `Q^(-1/n)` for
  nonnegative vectors of norm at most `R^K`.
- [`bakerHarman_lattice_approximation`](BakerHarman/DimensionInduction.lean) retains
  the earlier lattice interface with an existential logarithmic degree.

## Build and verify

Install Lean through Elan; `lean-toolchain` pins Lean 4.34.0 and the Lake manifest
pins Mathlib and its dependencies. From this directory run:

```sh
lake exe cache get
lake build
python3 scripts/check_baker_harman_sources.py
lake env lean scripts/CheckAxioms.lean
```

The source check verifies the sixteen vendored files, upstream and local hashes,
import-only relocation, and exact dependency closure. It works both in a standalone
checkout and under Lake's `.lake/packages` directory. The axiom audit checks every
library declaration, including private/generated declarations, and the imported
`OAI.Problem337` and `OAI.Erdos3` declarations. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed; proofs contain no `sorry` or custom axioms.

The library has no dependency on the shifted-sets project or its Jacobsthal library.

## Use as a dependency

For a sibling checkout, add this to the consuming project's `lakefile.toml`:

```toml
[[require]]
name = "baker_harman_small_remainders"
path = "../baker-harman-small-remainders"
```

Then run `lake update baker_harman_small_remainders` and import
`BakerHarman.TheoremTwo`. For a published revision, replace `path` with
`git = "https://github.com/jasondavies/baker-harman-small-remainders"` and set `rev`
to the full commit hash containing the results you need.

## Proof structure and exponent comparison

The paper's explicit exponent uses a rounded derivative order. For noninteger
`K > 1`, its `c(K)` is smaller than the shifted-sets exponent `γ(K)`; for example,
at `K = 3/2` they are `1/12` and approximately `0.1367`, respectively.
[`originalExponent_le_gammaBH`](BakerHarman/OriginalTheorem.lean) proves the
comparison. Both original theorems follow from their stronger versions by
restricting the power range.

[`Exponent.lean`](BakerHarman/Exponent.lean) proves that the exponent pair in the
original Lemma 1 retains saving at least `4γ(K)/3` before the paper weakens it.
The implemented analytic argument starts with the second-derivative estimate in
[`ReciprocalSum.lean`](BakerHarman/ReciprocalSum.lean), develops higher derivatives
by van der Corput differencing, and combines numerator bands. The resulting
[`ExponentialSum.lean`](BakerHarman/ExponentialSum.lean) bound has saving `6γ(K)/5`.
Allowing fixed logarithmic factors in the numerator retains saving `23γ(K)/20`.

[`PowerSlack.lean`](BakerHarman/PowerSlack.lean) uses the gap
`23/20 − (11/10)(26/25) = 3/500` to extend the large-sum frequency bound to
`Q ≤ R^((26/25)γ(K))`. Gaussian detection and dyadic selection then give a short
dual vector with norm `O(log Q + 1)` and scalar product `O(R(log Q + 1))`.

The earlier induction preserved one power threshold exactly and paid for that
with larger logarithmic degrees. The new
[`SharpDimensionInduction.lean`](BakerHarman/SharpDimensionInduction.lean) instead
allows a slightly larger power exponent in the lower-dimensional problem,
remaining strictly inside the analytic range. This absorbs the logarithmic
covolume increase without spending extra logarithms in the reciprocal scale.
Each induction step costs one logarithm, giving degrees `d` and `d−1`.

[`WeightedCoordinateLattice.lean`](BakerHarman/Lattice/WeightedCoordinateLattice.lean)
uses the lattice with basis `ψᵢ⁻¹eᵢ`, proves its covolume is `∏ ψᵢ⁻¹`, controls
its minimum nonzero length, and converts a unit-ball approximation into the
individual tolerances. For small vectors,
[`WeightedDirichlet.lean`](BakerHarman/WeightedDirichlet.lean) partitions the
fractional-part cube into rectangular boxes. The denominator bound is the product
of their side counts; rounding leaves a uniform positive part of each coordinate's
error budget. [`WeightedBudget.lean`](BakerHarman/WeightedBudget.lean) proves the
resulting small-vector case, including dimension one.

[`UnequalWeights.lean`](BakerHarman/UnequalWeights.lean) combines both cases and
removes the coordinate-sign restriction. Finally,
[`OriginalTheorem.lean`](BakerHarman/OriginalTheorem.lean) converts `log Q + 1`
to the paper's `log Q` condition, absorbs the auxiliary `R` threshold into `C₁`,
and supplies the original rounded exponent and natural-parameter statement.

[`TheoremTwo.lean`](BakerHarman/TheoremTwo.lean) retains the lattice separation
factor `ρ⁻¹ = maxᵢ ψᵢ` in the sharp lattice bound. The maximum weighted coordinate
is bounded by the weighted Euclidean norm, so the paper's large-vector hypothesis
supplies the required norm threshold. The same logarithmic conversion and
threshold absorption give Theorem 2 with its original constants and degrees.

## Provenance and license

The equal-weight library was extracted from `gcd-shifted-sets` at commit
`cb6cd4f6c95edab17f182c0dd169625b83c63ad2`, preserving its proof arguments while
renaming module paths and namespaces. The full unequal-weight development was
added subsequently in this repository. See [NOTICE](NOTICE) for provenance.
The project is licensed under [Apache-2.0](LICENSE). The original paper is not
redistributed.

Sixteen analytic and lattice sources come from
[`openai/math`](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a)
at revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. Only their import paths are
relocated; their original namespaces remain `OAI.Problem337` and `OAI.Erdos3`.
Exact upstream provenance and hashes are recorded in
[vendor/baker-harman-analytics/UPSTREAM.json](vendor/baker-harman-analytics/UPSTREAM.json).
Additional adapted lattice modules retain individual attribution headers. No
additional external sources are introduced by the unequal-weight development.
