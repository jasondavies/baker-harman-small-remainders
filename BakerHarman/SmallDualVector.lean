import BakerHarman.SlackSmallDualVector

/-!
# Small dual vectors at the shifted-sets exponent

Specialize `bakerHarman_slack_small_dual_vector` to `Q ≤ R ^ gammaBH K`.
The Gaussian detection and dyadic selection argument is proved in
`SlackSmallDualVector`.
-/

namespace BakerHarman

/-- If the reciprocal orbit avoids the unit neighborhoods of a separated
lattice, there is a short dual vector with scalar product `O(R(log Q+1))`.
The thresholds and constants depend only on `d` and `K`. -/
theorem bakerHarman_small_dual_vector (d : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C Q₀ R₀ : ℝ, 0 < C ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (Q : ℝ), Q₀ ≤ Q → Q ≤ R ^ gammaBH K →
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E],
      Module.finrank ℝ E = d → ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖) → ZLattice.covolume Λ ≤ Q → ∀ y : E,
      ‖y‖ ≤ R ^ (K + 1) →
      (∀ r : ℤ, R ≤ r → (r : ℝ) ≤ 2 * R → ∀ m : Λ, 1 ≤ ‖(r : ℝ)⁻¹ • y - (m : E)‖) →
      ∃ p : E, p ∈ euclideanDualLattice Λ ∧ p ≠ 0 ∧
        ‖p‖ ≤ C * (Real.log Q + 1) ∧ |inner ℝ p y| ≤ C * R * (Real.log Q + 1) := by
  obtain ⟨C, Q₀, R₀, hC, hQ₀, hR₀, h⟩ := bakerHarman_slack_small_dual_vector d K hK
  refine ⟨C, Q₀, R₀, hC, hQ₀, hR₀, ?_⟩
  intro R hR Q hQ hQR
  exact h R hR Q hQ (hQR.trans (gammaBH_rpow_le_analyticPowerRange K R (by linarith)))

end BakerHarman
