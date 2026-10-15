import BakerHarman.Lattice.GaussianTail

/-!
# Gaussian mass of a separated lattice

Poisson summation gives a tail estimate proportional to the total Gaussian mass.
For a lattice with no nonzero vector shorter than one, the zero vector is the
only contribution outside this tail. Absorbing the tail gives a bound depending
only on the dimension, without a separate lattice packing theorem.
-/

namespace BakerHarman

open OAI.Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ Λ] in
/-- With minimum nonzero length at least one, the mass splits into its zero
term and the Gaussian tail outside the ball of radius `1/2`. -/
theorem separated_latticeGaussianMass_eq_one_add_tail {t : ℝ} (ht : 0 < t)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖) :
    latticeGaussianMass Λ t 0 = 1 + latticeGaussianTail Λ t (1 / 2) := by
  classical
  have h := (lattice_gaussian_summable Λ ht 0).tsum_eq_add_tsum_ite (0 : Λ)
  simp only [Submodule.coe_zero, sub_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero] at h
  change latticeGaussianMass Λ t 0 = _ at h
  rw [h]
  congr 1
  apply tsum_congr
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hx0 : (x : E) ≠ 0 := by intro he; exact hx (Subtype.ext he)
    have hn : (1 / 2 : ℝ) < ‖(x : E)‖ := by linarith [hsep x x.property hx0]
    simp only [ite_eq_right hx, ite_eq_left hn, zero_sub, norm_neg]

private lemma gaussian_separation_coefficient (d : ℕ) (t : ℝ)
    (ht : 8 * ((d : ℝ) + 1) ≤ t) :
    Real.exp (-Real.pi * t / 8) * (2 : ℝ) ^ d ≤ 1 / 2 := by
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have htwo : (2 : ℝ) ^ d ≤ Real.exp (d : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he d
    simpa only [← Real.exp_nat_mul, mul_one] using h
  have hexp : -Real.pi * t / 8 + d ≤ -1 := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) ht0]
  have hhalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
  calc
    _ ≤ Real.exp (-Real.pi * t / 8) * Real.exp (d : ℝ) :=
      mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
    _ = Real.exp (-Real.pi * t / 8 + d) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr hexp
    _ ≤ _ := hhalf

/-- The Gaussian mass is at most two at all temperatures above an explicit
dimension-dependent threshold, uniformly over lattices of minimum length one. -/
theorem latticeGaussianMass_le_two_of_separated (t : ℝ)
    (ht : 8 * ((Module.finrank ℝ E : ℝ) + 1) ≤ t)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖) :
    latticeGaussianMass Λ t 0 ≤ 2 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  have htail := latticeGaussianTail_bound Λ ht0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : -Real.pi * t * (1 / 2 : ℝ) ^ 2 / 2 = -Real.pi * t / 8 := by ring
  rw [he] at htail
  have hcoef := gaussian_separation_coefficient (Module.finrank ℝ E) t ht
  have hnonneg := latticeGaussianMass_nonneg Λ t 0
  have hmass := separated_latticeGaussianMass_eq_one_add_tail Λ ht0 hsep
  nlinarith [mul_le_mul_of_nonneg_right hcoef hnonneg]

end BakerHarman
