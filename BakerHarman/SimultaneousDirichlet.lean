import BakerHarman.WeightedDirichlet
import BakerHarman.Defs

/-!
# Simultaneous Dirichlet approximation

Partition the fractional-part cube into `M ^ card ι` boxes and apply the
pigeonhole principle to one more multiple. The denominator and every coordinate
error are explicit, as required for the final reciprocal approximation argument.
-/

namespace BakerHarman

/-- Simultaneous approximation with denominator at most `M ^ card ι` and
coordinate error strictly less than `1 / M`. -/
theorem simultaneous_dirichlet {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (hM : 0 < M) :
    ∃ l : ℕ, 0 < l ∧ l ≤ M ^ Fintype.card ι ∧
      ∃ p : ι → ℤ, ∀ i, |(l : ℝ) * x i - (p i : ℝ)| < 1 / M := by
  simpa using weighted_simultaneous_dirichlet x (fun _ => M) (fun _ => hM)

end BakerHarman
