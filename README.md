# Baker–Harman small remainders

A Lean 4 / Mathlib formalisation of equal-weight small remainders, following and
adapting the strategy of:

> R. C. Baker and G. Harman, *Small remainder of a vector to suitable modulus*,
> Math. Z. 221 (1996), 59–71, [doi:10.1007/BF02622099](https://doi.org/10.1007/BF02622099).

The main theorem uses the exponent quoted in Lemma 5 of Heyman–Shparlinski,
*On the greatest common divisor of shifted sets*, J. Number Theory 154 (2015),
63–73, [doi:10.1016/j.jnt.2015.02.012](https://doi.org/10.1016/j.jnt.2015.02.012).

**Scope:** the equal-weight theorem and a general large-vector lattice
approximation theorem are proved. This is an adaptation of the original argument,
not a complete formalisation of the paper's unequal-weight theorem.

## Main results

Import `BakerHarman.EqualWeights` for the main application, or `BakerHarman` for
the entire library. Declarations live in the `BakerHarman` namespace.

- [`bakerHarman_equal_weights`](BakerHarman/EqualWeights.lean): for `n ≥ 2`,
  `K ≥ 1`, sufficiently large real `Q,R`, `Q ≤ R^γ(K)`, and a nonnegative real
  vector `a` with Euclidean norm at most `R^K`, there is a natural modulus
  `R ≤ r ≤ 2QR` such that `distNearestInt (aᵢ/r) ≤ Q^(-1/n)` for every coordinate.
  Here `γ(K) = 1 / (2^(2 + max(1,K)) - 4)`.
- [`bakerHarman_lattice_approximation`](BakerHarman/DimensionInduction.lean):
  large-vector reciprocal approximation in every positive dimension, uniformly
  over real inner product spaces and full lattices, with the precise hypotheses
  recorded in `ReciprocalLatticeStatement`.

The library also contains reciprocal exponential-sum estimates, Gaussian Fourier
lattice detection, hyperplane lattice geometry, and simultaneous approximation.
It has no dependency on the shifted-sets project or its Jacobsthal library.

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
import-only relocation, and exact dependency closure. The axiom audit checks every
library declaration, including private/generated declarations, and the imported
`OAI.Problem337` and `OAI.Erdos3` declarations. Only `propext`, `Classical.choice`,
and `Quot.sound` are allowed; proofs contain no `sorry` or custom axioms.

## Use as a local dependency

For a sibling checkout, add this to the consuming project's `lakefile.toml`:

```toml
[[require]]
name = "baker_harman_small_remainders"
path = "../baker-harman-small-remainders"
```

Then run `lake update baker_harman_small_remainders` and import
`BakerHarman.EqualWeights`. Once published, consumers can replace `path` with
`git` and a pinned commit in `rev`.

## Proof and exponent comparison

There is an exponent discrepancy between the shifted-sets lemma and its cited theorem.
[Baker–Harman, *Small remainder of a vector to suitable modulus*, Math. Z. 221 (1996), 59–71](https://doi.org/10.1007/BF02622099),
p. 62, equation (2.1), gives `c(K) = 1 / (2^(k + 1) - 4)` with
`k = ⌈1 + max{K,1}⌉`, and explicitly uses this constant in its Theorem 1.
The shifted-sets paper's Lemma 5 (p. 67), and our `gammaBH`, instead use
`γ(K) = 1 / (2^(2 + max{1,K}) - 4)`. For noninteger `K > 1`, this allows a larger
range `Q ≤ R^γ(K)` than the original theorem supplies: at `K = 3/2`,
`c(K) = 1/12 ≈ 0.0833`, whereas `γ(K) ≈ 0.1367`.
Thus the original theorem as stated does not supply the power range used here.

The original **proof**, however, has enough numerical slack to accommodate `γ(K)`.
Before weakening its estimate to `R^(1-2c(K))`, the exponent pair in Lemma 1 gives
saving `s(K) = (k - max{1,K}) / (2^k - 2)`.
[`Exponent.lean`](BakerHarman/Exponent.lean) proves
`s(K) ≥ 4γ(K)/3`. Choosing the small-sum cutoff `R Q^(-5/4)` in Proposition 3
leaves a positive margin `s(K) - 5γ(K)/4 ≥ γ(K)/12`; the module also proves that
any fixed multiple of `R^(1-s(K))` is eventually at most half this cutoff,
uniformly for `0 < Q ≤ R^γ(K)`. This supplies the exponent bookkeeping needed to
adapt the original proof without changing `γ`, `κ` or `ϑ`.
The completed proof below retains that power range through the analytic estimates,
lattice induction, and final equal-weight approximation.

The analytic proof starts in
[`BakerHarman/ReciprocalSum.lean`](BakerHarman/ReciprocalSum.lean).
It proves the base-order estimate `|Σ e(z/r)| ≤ 252(√R + R²/|z|)` for
`0 < |z| ≤ R²` on natural subintervals of `[R,2R)`, including real `R ≥ 1`.
[`BakerHarman/HigherDerivative.lean`](BakerHarman/HigherDerivative.lean)
also proves explicit bounds at every higher derivative order, using an optimized
van der Corput induction. [`BakerHarman/PowerBands.lean`](BakerHarman/PowerBands.lean)
converts them to power savings on explicit numerator bands and combines finite chains
of overlapping bands. [`BakerHarman/BandSelection.lean`](BakerHarman/BandSelection.lean)
selects bands covering the full range, and
[`BakerHarman/ExponentialSum.lean`](BakerHarman/ExponentialSum.lean)
proves `|Σ e(z/r)| ≤ C(R^(1-6γ(K)/5) + R²/|z|)` for
`0 < |z| ≤ R^(K+1)`, `K ≥ 1`, on closed integer subintervals of `[R,2R]`.
Allowing any fixed factor in the numerator range retains saving `23γ(K)/20`
for sufficiently large `R`. [`BakerHarman/LargeSums.lean`](BakerHarman/LargeSums.lean)
then proves that a sum of size at least `T ≥ R Q^(-11/10)` has
`|z| ≤ C R²/T`, uniformly for `0 < Q ≤ R^γ(K)`. This completes the analytic
input to the lattice argument, using a different saving and cutoff from the
original exponent-pair bookkeeping above.
[`BakerHarman/DyadicSelection.lean`](BakerHarman/DyadicSelection.lean)
proves the finite counting steps: discarding small sums, selecting a dyadic class,
bounding the number of classes logarithmically, and finding a small scalar product
or a small difference by the box argument, including singleton classes.
The derivative, differencing and basic lattice definitions use sixteen Apache-2.0 sources from the
same pinned `openai/math` revision, in `vendor/baker-harman-analytics`.
Only their import paths are relocated to avoid overlapping Lake module roots;
`python3 scripts/check_baker_harman_sources.py` verifies local and upstream hashes,
the import-only relocation, and the exact dependency closure. The axiom audit below
also checks every imported declaration in their `OAI.Problem337` and `OAI.Erdos3` namespaces.

[`BakerHarman/Lattice/DetectionBudget.lean`](BakerHarman/Lattice/DetectionBudget.lean)
proves a Gaussian alternative to the original Fourier detection lemma. For any
dimension `d`, its threshold is uniform over ambient inner product spaces and
lattices with minimum nonzero length at least one and covolume at most `Q`.
A finite sequence avoiding the unit neighborhoods has Fourier-sum mass at least
one quarter of its length among nonzero dual vectors of length `O_d(log Q + 1)`;
there are at most `O_d(Q(log Q + 1)^d)` such vectors.
The local `Lattice` modules extract and adapt the required Poisson and integration
proofs from the same pinned `openai/math` revision, with source attribution and
the upstream Apache-2.0 license retained. They avoid its unrelated import branches.
[`BakerHarman/LogFactors.lean`](BakerHarman/LogFactors.lean) absorbs fixed
logarithmic powers in the numerator range, retaining saving `23γ(K)/20`.
The small-sum removal lemma also accommodates logarithmic factors in the frequency
count. [`BakerHarman/SmallDualVector.lean`](BakerHarman/SmallDualVector.lean)
combines these estimates: failure of reciprocal approximation produces a nonzero
dual vector of length `O(log Q + 1)` with scalar product `O(R(log Q + 1))`.
The constants are uniform over ambient spaces and lattices of a fixed dimension.
[`BakerHarman/DimensionOne.lean`](BakerHarman/DimensionOne.lean)
proves the one-dimensional large-vector approximation case. The lattice modules
also prove primitive-normal reduction, the exact hyperplane covolume formula,
dual norm and covolume lower bounds, scaling, and lifting approximations from a
scaled hyperplane lattice.
[`BakerHarman/DimensionInduction.lean`](BakerHarman/DimensionInduction.lean)
proves the large-vector approximation in every positive dimension, with constants
and a logarithmic degree depending only on the dimension and `K`. The induction
preserves `Q ≤ R^γ(K)` exactly; its output interval is bounded by
`B R Q (log Q + 1)^m / ρ`, where `ρ ≥ 1` is a lower bound for nonzero lattice lengths.
[`BakerHarman/SimultaneousDirichlet.lean`](BakerHarman/SimultaneousDirichlet.lean)
proves simultaneous approximation by a finite pigeonhole argument.
[`BakerHarman/SmallVectorEqualWeights.lean`](BakerHarman/SmallVectorEqualWeights.lean)
uses it and reciprocal rounding to cover small vectors. Finally, `EqualWeights.lean`
combines both cases: equal coordinate tolerances absorb the fixed logarithmic powers,
and both cases produce a modulus in `[R,2QR]`. The shifted-sets application is maintained separately in `gcd-shifted-sets`.

## Provenance and license

Extracted from `gcd-shifted-sets` at commit
`cb6cd4f6c95edab17f182c0dd169625b83c63ad2`. Module paths and namespaces were renamed;
the proof arguments were preserved. See [NOTICE](NOTICE) for extraction and
upstream provenance. The project is licensed under [Apache-2.0](LICENSE).
The original paper is not redistributed.
