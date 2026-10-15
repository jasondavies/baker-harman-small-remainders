import BakerHarman.Lattice.DualCounting
import BakerHarman.Lattice.FourierMass

/-!
# Fourier detection for a sequence avoiding a lattice

If every point of a finite sequence is at distance at least one from the lattice,
a Gaussian with a sufficiently small spatial tail has small average. Poisson
summation and a bound on the dual tail then force substantial exponential-sum
mass among the nonzero dual vectors in a finite ball.
-/

namespace BakerHarman

open OAI.Erdos3 Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- Gaussian Fourier detection, with explicit spatial and spectral tail budgets.
The sequence is arbitrary; in Baker–Harman it will be `y/r`. -/
theorem lattice_fourier_detection {ι : Type*} (s : Finset ι) (x : ι → E)
    (t H : ℝ) (ht : 0 < t) (hH : 0 ≤ H)
    (hfar : ∀ i ∈ s, ∀ m : Λ, 1 ≤ ‖x i - (m : E)‖)
    (hspatial : Real.exp (-Real.pi * t / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
      normalizedLatticeGaussian Λ t 0 ≤ 1 / 2)
    (hspectral : Real.exp (-Real.pi / t * H ^ 2 / 2) * (2 : ℝ) ^ Module.finrank ℝ E *
      normalizedLatticeGaussian Λ t 0 ≤ 1 / 4) :
    (s.card : ℝ) / 4 ≤ ∑ ξ ∈ (dualBall Λ H).erase 0,
      ‖∑ i ∈ s, euclideanCharacter (ξ : E) (x i)‖ := by
  classical
  let w : euclideanDualLattice Λ → ℝ := fun ξ => Real.exp (-Real.pi / t * ‖(ξ : E)‖ ^ 2)
  let c : euclideanDualLattice Λ → ℂ := fun ξ => ∑ i ∈ s, euclideanCharacter (ξ : E) (x i)
  have hw : Summable w := by
    simpa only [w, zero_sub, norm_neg, div_eq_mul_inv] using
      lattice_gaussian_summable (euclideanDualLattice Λ) (inv_pos.mpr ht) 0
  have hwpos (ξ : euclideanDualLattice Λ) : 0 ≤ w ξ := (Real.exp_pos _).le
  have hwle (ξ : euclideanDualLattice Λ) : w ξ ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr Real.pi_pos.le) ht.le) (sq_nonneg _)
  have hc (ξ : euclideanDualLattice Λ) : ‖c ξ‖ ≤ s.card := by
    calc
      _ ≤ ∑ i ∈ s, ‖euclideanCharacter (ξ : E) (x i)‖ := norm_sum_le _ _
      _ = _ := by simp
  have htail : (∑' ξ, if ξ ∈ dualBall Λ H then 0 else w ξ) ≤ (1 / 4 : ℝ) := by
    have h := latticeGaussianTail_bound (euclideanDualLattice Λ) (inv_pos.mpr ht) hH
    rw [← normalizedLatticeGaussian_zero_eq_dual Λ ht] at h
    have he : (∑' ξ, if ξ ∈ dualBall Λ H then 0 else w ξ) =
        latticeGaussianTail (euclideanDualLattice Λ) t⁻¹ H := by
      apply tsum_congr
      intro ξ
      simp only [mem_dualBall, w, ← not_lt, ite_not, div_eq_mul_inv]
    rw [he]
    exact h.trans (by simpa only [div_eq_mul_inv] using hspectral)
  have hfourier : (∑' ξ, (w ξ : ℂ) * c ξ) =
      ∑ i ∈ s, (normalizedLatticeGaussian Λ t (x i) : ℂ) := by
    simp only [w, c, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (s := s) (fun i _ => latticeGaussian_fourier_summable Λ ht (x i))]
    simp only [← normalizedLatticeGaussian_poisson Λ ht]
  have hpoint (i : ι) (hi : i ∈ s) : normalizedLatticeGaussian Λ t (x i) ≤ 1 / 2 := by
    have h := normalizedLatticeGaussian_le_of_far Λ ht (by norm_num : (0 : ℝ) ≤ 1)
      (x i) (hfar i hi)
    simp only [one_pow, mul_one] at h
    exact h.trans hspatial
  have hsmall : (∑' ξ, (w ξ : ℂ) * c ξ).re ≤ (s.card : ℝ) / 2 := by
    rw [hfourier, Complex.re_sum]
    simp only [Complex.ofReal_re]
    have h := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one_div] using h
  exact finite_fourier_mass (dualBall Λ H) 0 (by simpa using hH) w c s.card
    (Nat.cast_nonneg _) hw hwpos hwle (by simp [w])
    (by simp [c, euclideanCharacter]) hc htail hsmall

end BakerHarman
