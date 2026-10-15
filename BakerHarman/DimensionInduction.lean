import BakerHarman.SharpDimensionInduction

/-!
# Lattice approximation at the shifted-sets exponent

Specialize the sharp lattice theorem to `gammaBH K`, exposing an existential
logarithmic degree for the equal-weight approximation argument.
-/

namespace BakerHarman

universe u

/-- The sharp lattice statement specialized to `gammaBH K`. -/
abbrev ReciprocalLatticeStatement (d : ℕ) (K : ℝ) (m : ℕ) (A B Q₀ R₀ : ℝ) : Prop :=
  PowerLatticeStatement.{u} d K (gammaBH K) m A B Q₀ R₀

/-- Reciprocal approximation for large vectors in every positive dimension.
The logarithmic degree and constants depend only on `d` and `K`. -/
theorem bakerHarman_lattice_approximation (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 1 ≤ K) :
    ∃ (m : ℕ) (A B Q₀ R₀ : ℝ), 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ReciprocalLatticeStatement.{u} d K m A B Q₀ R₀ := by
  obtain ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩ :=
    bakerHarman_sharp_lattice_approximation.{u} d hd K hK (gammaBH K)
      (gammaBH_pos K) (gammaBH_lt_analyticPowerRange K)
  exact ⟨d - 1, A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩

end BakerHarman
