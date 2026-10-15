import BakerHarman.Lattice.Scaling
import BakerHarman.Lattice.SeparatedMass

/-!
# Covolume lower bounds from separation

The zero term on the dual side of Poisson summation bounds the covolume below.
Scaling then gives a bound in terms of any lower bound for nonzero lengths.
-/

namespace BakerHarman

open OAI.Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def latticeDimensionFactor (d : ℕ) : ℝ :=
  2 * (Real.sqrt (8 * ((d : ℝ) + 1))) ^ d

theorem latticeDimensionFactor_pos (d : ℕ) : 0 < latticeDimensionFactor d := by
  unfold latticeDimensionFactor; positivity

omit [MeasurableSpace E] [BorelSpace E] in
theorem one_le_latticeGaussianMass_zero (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    {t : ℝ} (ht : 0 < t) : 1 ≤ latticeGaussianMass Λ t 0 := by
  have h : Real.exp (-Real.pi * t * ‖(0 : E) - ((0 : Λ) : E)‖ ^ 2) ≤
      latticeGaussianMass Λ t 0 :=
    (lattice_gaussian_summable Λ ht (0 : E)).le_tsum (0 : Λ)
    (fun _ _ => (Real.exp_pos _).le)
  simpa only [Submodule.coe_zero, sub_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero] using h

theorem one_le_factor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hsep : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖) :
    1 ≤ latticeDimensionFactor (Module.finrank ℝ E) * ZLattice.covolume Λ := by
  let T : ℝ := 8 * ((Module.finrank ℝ E : ℝ) + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hl := one_le_latticeGaussianMass_zero (euclideanDualLattice Λ) (inv_pos.mpr hT)
  rw [← normalizedLatticeGaussian_zero_eq_dual Λ hT] at hl
  have hu := latticeGaussianMass_le_two_of_separated Λ T le_rfl hsep
  have h := mul_le_mul_of_nonneg_left hu (latticeGaussianNormalizer_nonneg Λ T)
  dsimp only [normalizedLatticeGaussian, latticeGaussianNormalizer] at hl h
  dsimp only [latticeDimensionFactor]
  nlinarith [hl.trans h]

theorem separation_pow_le_factor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ρ ≤ ‖x‖) :
    ρ ^ Module.finrank ℝ E ≤
      latticeDimensionFactor (Module.finrank ℝ E) * ZLattice.covolume Λ := by
  have hs : ∀ x ∈ scaledLattice Λ ρ⁻¹ (inv_ne_zero hρ.ne'), x ≠ 0 → 1 ≤ ‖x‖ := by
    simpa only [inv_mul_cancel₀ hρ.ne'] using scaledLattice_separation Λ ρ⁻¹ (inv_pos.mpr hρ) ρ hsep
  have h := one_le_factor_mul_covolume _ hs
  rw [scaledLattice_covolume Λ ρ⁻¹ (inv_pos.mpr hρ), inv_pow] at h
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg hρ.le (Module.finrank ℝ E))
  have he : ρ ^ Module.finrank ℝ E *
      (latticeDimensionFactor (Module.finrank ℝ E) *
        ((ρ ^ Module.finrank ℝ E)⁻¹ * ZLattice.covolume Λ)) =
      latticeDimensionFactor (Module.finrank ℝ E) * ZLattice.covolume Λ := by
    field_simp
  simpa only [mul_one, he] using hh

/-- In positive dimension, a separation parameter at least one is bounded by
a dimension-dependent multiple of the covolume. -/
theorem separation_le_factor_mul_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hdim : 0 < Module.finrank ℝ E) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ρ ≤ ‖x‖) :
    ρ ≤ latticeDimensionFactor (Module.finrank ℝ E) * ZLattice.covolume Λ := by
  exact (le_self_pow₀ hρ (Nat.ne_of_gt hdim)).trans
    (separation_pow_le_factor_mul_covolume Λ ρ (lt_of_lt_of_le zero_lt_one hρ) hsep)

/-- The short search interval is contained in the covolume/separation interval
used in dimension induction. -/
theorem reciprocal_interval_le_covolume_separation (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hdim : 0 < Module.finrank ℝ E) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ρ ≤ ‖x‖)
    (R Q : ℝ) (hR : 0 ≤ R) (hQ : ZLattice.covolume Λ ≤ Q) :
    2 * R ≤ 2 * latticeDimensionFactor (Module.finrank ℝ E) * R * Q / ρ := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have h := (separation_le_factor_mul_covolume Λ hdim ρ hρ hsep).trans
    (mul_le_mul_of_nonneg_left hQ (latticeDimensionFactor_pos _).le)
  apply (le_div_iff₀ hρ0).mpr
  have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * R by positivity)
  nlinarith [hh]

end BakerHarman
