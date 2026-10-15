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
  obtain ⟨C, Q₀, R₀, hC, hQ₀, hR₀, hsmall⟩ := bakerHarman_small_dual_vector 1 K hK
  let δ := Real.exp (-Real.pi) / latticeDimensionFactor 1
  have hδ : 0 < δ := div_pos (Real.exp_pos _) (latticeDimensionFactor_pos 1)
  let A := C / δ + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, Q₀, R₀, hA, hQ₀, hR₀, ?_⟩
  intro R hR Q hQ hQR E _ _ _ _ _ hdim Λ _ _ hsep hcov y hylo hyhi
  have hR0 : 0 < R := by linarith
  have hQ1 : 1 ≤ Q := hQ₀.trans hQ
  have hQ0 : 0 < Q := by linarith
  have hlog : 0 < Real.log Q + 1 := by linarith [Real.log_nonneg hQ1]
  by_contra hfail
  push Not at hfail
  obtain ⟨p, hpΛ, hp, _, hinner⟩ := hsmall R hR Q hQ hQR E hdim Λ hsep hcov y hyhi hfail
  have hdual : δ ≤ ‖p‖ * ZLattice.covolume Λ := by
    simpa only [hdim, δ, latticeDimensionFactor] using
      dual_norm_mul_covolume_lower_bound Λ hsep p hpΛ hp
  have hpQ : δ ≤ ‖p‖ * Q := hdual.trans (mul_le_mul_of_nonneg_left hcov (norm_nonneg _))
  have hn := norm_eq_abs_inner_div_norm_of_finrank_one hdim p y hp
  have hnorm : ‖y‖ * ‖p‖ = |inner ℝ p y| := (eq_div_iff (norm_ne_zero_iff.mpr hp)).mp hn
  have hupper : δ * ‖y‖ ≤ C * R * Q * (Real.log Q + 1) := by
    calc
      _ ≤ (‖p‖ * Q) * ‖y‖ := mul_le_mul_of_nonneg_right hpQ (norm_nonneg _)
      _ = Q * |inner ℝ p y| := by rw [← hnorm]; ring
      _ ≤ Q * (C * R * (Real.log Q + 1)) := mul_le_mul_of_nonneg_left hinner hQ0.le
      _ = _ := by ring
  have hlower := mul_le_mul_of_nonneg_left hylo hδ.le
  have hAδ : δ * A = C + δ := by dsimp [A]; field_simp
  have he : δ * (A * R * Q * (Real.log Q + 1)) =
      (C + δ) * R * Q * (Real.log Q + 1) := by rw [← hAδ]; ring
  rw [he] at hlower
  have hpos : 0 < δ * R * Q * (Real.log Q + 1) := by positivity
  nlinarith [hlower.trans hupper]

end BakerHarman
