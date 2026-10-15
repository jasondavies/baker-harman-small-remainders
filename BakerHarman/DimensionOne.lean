import BakerHarman.SlackDimensionOne
import BakerHarman.SmallDualVector
import BakerHarman.Lattice.DualLowerBound
import BakerHarman.Lattice.CovolumeLowerBound

/-!
# The one-dimensional reciprocal approximation step

A failed approximation produces a dual vector with small scalar product.
In dimension one that scalar product, together with the dual norm lower bound,
forces the original vector to be small. This is the base of dimension induction.
-/

namespace BakerHarman

/-- A sufficiently large vector in a one-dimensional lattice has a reciprocal
approximation already in `[R, 2R]`. Constants are uniform over the ambient space. -/
theorem bakerHarman_dimension_one (K : ℝ) (hK : 1 ≤ K) :
    ∃ A Q₀ R₀ : ℝ, 0 < A ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (Q : ℝ), Q₀ ≤ Q → Q ≤ R ^ gammaBH K →
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E],
      Module.finrank ℝ E = 1 → ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖) → ZLattice.covolume Λ ≤ Q → ∀ y : E,
      A * R * Q * (Real.log Q + 1) ≤ ‖y‖ → ‖y‖ ≤ R ^ (K + 1) →
      ∃ r : ℤ, R ≤ r ∧ (r : ℝ) ≤ 2 * R ∧ ∃ m : Λ, ‖(r : ℝ)⁻¹ • y - (m : E)‖ < 1 := by
  obtain ⟨A, Q₀, R₀, hA, hQ₀, hR₀, h⟩ := bakerHarman_slack_dimension_one K hK
  refine ⟨A, Q₀, R₀, hA, hQ₀, hR₀, ?_⟩
  intro R hR Q hQ hQR
  exact h R hR Q hQ (hQR.trans (Real.rpow_le_rpow_of_exponent_le
    (by linarith) (gammaBH_lt_analyticPowerRange K).le))

end BakerHarman
