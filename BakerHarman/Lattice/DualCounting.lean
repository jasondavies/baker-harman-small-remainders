import BakerHarman.Lattice.SeparatedMass

/-!
# Counting short dual lattice vectors

Poisson summation at temperature `H²` bounds the dual Gaussian at temperature
`H⁻²`. Every dual vector of length at most `H` has weight at least `exp(-π)`,
so the mass estimate gives a count proportional to `covolume * H^dimension`.
-/

namespace BakerHarman

open OAI.Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A bounded set of dual lattice vectors is finite. -/
theorem finite_dual_norm_le (H : ℝ) :
    Set.Finite {ξ : euclideanDualLattice Λ | ‖(ξ : E)‖ ≤ H} := by
  let : DiscreteTopology (euclideanDualLattice Λ).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (euclideanDualLattice Λ))
  let : DiscreteTopology (euclideanDualLattice Λ : Set E) :=
    inferInstanceAs (DiscreteTopology (euclideanDualLattice Λ))
  have hclosed : IsClosed (euclideanDualLattice Λ : Set E) :=
    (euclideanDualLattice Λ).toAddSubgroup.isClosed_of_discreteTopology
  have hfinite := Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall (x := (0 : E)) (r := H)) hclosed
  apply (hfinite.preimage_embedding (.subtype _)).subset
  intro ξ hξ
  exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hξ, ξ.property⟩

/-- The finite ball in the dual lattice, including zero when `H ≥ 0`. -/
noncomputable def dualBall (H : ℝ) : Finset (euclideanDualLattice Λ) :=
  (finite_dual_norm_le Λ H).toFinset

omit [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem mem_dualBall (H : ℝ) (ξ : euclideanDualLattice Λ) :
    ξ ∈ dualBall Λ H ↔ ‖(ξ : E)‖ ≤ H := Set.Finite.mem_toFinset _

/-- Uniform count for finite families of short dual vectors. -/
theorem dual_card_le_of_separated (H : ℝ) (hH : 0 < H)
    (ht : 8 * ((Module.finrank ℝ E : ℝ) + 1) ≤ H ^ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖)
    (s : Finset (euclideanDualLattice Λ)) (hs : ∀ ξ ∈ s, ‖(ξ : E)‖ ≤ H) :
    (s.card : ℝ) ≤ 2 * Real.exp Real.pi * H ^ Module.finrank ℝ E * ZLattice.covolume Λ := by
  have htemp : 0 < (H ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hH)
  have hterm (ξ : euclideanDualLattice Λ) (hξ : ξ ∈ s) :
      Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * (H ^ 2)⁻¹ * ‖(0 : E) - ξ‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    simp only [zero_sub, norm_neg]
    have hn : ‖(ξ : E)‖ ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hs ξ hξ) 2
    have hr : (H ^ 2)⁻¹ * ‖(ξ : E)‖ ^ 2 ≤ 1 := by
      rw [inv_mul_eq_div, div_le_one (sq_pos_of_pos hH)]
      exact hn
    nlinarith [mul_le_mul_of_nonneg_left hr Real.pi_pos.le]
  have hsum := (Finset.sum_le_sum hterm).trans
    ((lattice_gaussian_summable (euclideanDualLattice Λ) htemp 0).sum_le_tsum s
      (fun _ _ => (Real.exp_pos _).le))
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  change (s.card : ℝ) * Real.exp (-Real.pi) ≤
    latticeGaussianMass (euclideanDualLattice Λ) (H ^ 2)⁻¹ 0 at hsum
  rw [← normalizedLatticeGaussian_zero_eq_dual Λ (sq_pos_of_pos hH)] at hsum
  have hm := latticeGaussianMass_le_two_of_separated Λ (H ^ 2) ht hsep
  have hnormal : latticeGaussianNormalizer Λ (H ^ 2) =
      H ^ Module.finrank ℝ E * ZLattice.covolume Λ := by
    rw [latticeGaussianNormalizer, Real.sqrt_sq hH.le]
  have hmass : normalizedLatticeGaussian Λ (H ^ 2) 0 ≤
      2 * H ^ Module.finrank ℝ E * ZLattice.covolume Λ := by
    unfold normalizedLatticeGaussian
    rw [hnormal]
    have h := mul_le_mul_of_nonneg_left hm (latticeGaussianNormalizer_nonneg Λ (H ^ 2))
    rw [hnormal] at h
    nlinarith only [h]
  have h := mul_le_mul_of_nonneg_right (hsum.trans hmass) (Real.exp_pos Real.pi).le
  have he : Real.exp (-Real.pi) * Real.exp Real.pi = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [mul_assoc, he, mul_one] at h
  nlinarith only [h]

end BakerHarman
