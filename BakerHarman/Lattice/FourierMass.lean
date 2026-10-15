import Mathlib

/-!
# Finite Fourier mass after truncation

A small weighted Fourier sum with a prescribed zero coefficient must have
substantial mass in its other coefficients. A bound on the discarded weights
localizes that mass to a finite set. This formulation retains the total mass
needed by the dyadic box argument, rather than extracting just one coefficient.
-/

namespace BakerHarman

/-- Finite mass extraction from a weighted Fourier identity. -/
theorem finite_fourier_mass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι) (hz : z ∈ s) (w : ι → ℝ) (c : ι → ℂ)
    (N : ℝ) (hN : 0 ≤ N) (hw : Summable w)
    (hwpos : ∀ i, 0 ≤ w i) (hwle : ∀ i, w i ≤ 1)
    (hwz : w z = 1) (hcz : c z = N) (hc : ∀ i, ‖c i‖ ≤ N)
    (htail : (∑' i, if i ∈ s then 0 else w i) ≤ 1 / 4)
    (hsmall : (∑' i, (w i : ℂ) * c i).re ≤ N / 2) :
    N / 4 ≤ ∑ i ∈ s.erase z, ‖c i‖ := by
  classical
  let tail : ι → ℝ := fun i => if i ∈ s then 0 else w i
  let mass : ι → ℝ := fun i => if i ∈ s.erase z then ‖c i‖ else 0
  have ht : Summable tail := by
    convert hw.indicator {i | i ∉ s} using 1
    funext i
    simp only [tail, Set.indicator_apply, Set.mem_ofPred_eq, ite_not]
  have hm : HasSum mass (∑ i ∈ s.erase z, ‖c i‖) := by
    have h : HasSum mass (∑ i ∈ s.erase z, mass i) :=
      hasSum_sum_of_ne_finset_zero (s := s.erase z) (f := mass)
      (fun i hi => by simp only [mass, ite_eq_right hi])
    simpa only [mass, Finset.sum_ite_mem, Finset.inter_self] using h
  have hsum : Summable (fun i => (w i : ℂ) * c i) := by
    apply (hw.mul_right N).of_norm_bounded
    intro i
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hwpos i)]
    exact mul_le_mul_of_nonneg_left (hc i) (hwpos i)
  have hr : Summable (fun i => ((w i : ℂ) * c i).re) :=
    (Complex.hasSum_re hsum.hasSum).summable
  let f : ι → ℝ := fun i => ((w i : ℂ) * c i).re + mass i + N * tail i
  have hf : Summable f := (hr.add hm.summable).add (ht.mul_left N)
  have hnonneg (i : ι) : 0 ≤ f i := by
    have hre : -‖c i‖ ≤ (c i).re := (abs_le.mp (Complex.abs_re_le_norm (c i))).1
    by_cases hi : i = z
    · subst i
      simpa [f, mass, tail, hwz, hcz, hz] using hN
    · by_cases his : i ∈ s
      · have him : i ∈ s.erase z := Finset.mem_erase.mpr ⟨hi, his⟩
        simp only [f, mass, tail, ite_eq_left him, ite_eq_left his, mul_zero, add_zero,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith [mul_nonneg (hwpos i) (show 0 ≤ (c i).re + ‖c i‖ by linarith),
          mul_nonneg (sub_nonneg.mpr (hwle i)) (norm_nonneg (c i))]
      · have him : i ∉ s.erase z := fun h => his (Finset.mem_erase.mp h).2
        simp only [f, mass, tail, ite_eq_right him, ite_eq_right his, add_zero,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        nlinarith [mul_nonneg (hwpos i) (show 0 ≤ (c i).re + N by linarith [hc i])]
  have hfz : f z = N := by simp [f, mass, tail, hwz, hcz, hz]
  have hone : N ≤ ∑' i, f i := hfz ▸ hf.le_tsum z (fun i _ => hnonneg i)
  have hsplit : (∑' i, f i) = (∑' i, (w i : ℂ) * c i).re +
      (∑ i ∈ s.erase z, ‖c i‖) + N * ∑' i, tail i := by
    rw [show f = fun i => (((w i : ℂ) * c i).re + mass i) + N * tail i from rfl,
      Summable.tsum_add (hr.add hm.summable) (ht.mul_left N),
      Summable.tsum_add hr hm.summable, hm.tsum_eq, tsum_mul_left, ← Complex.re_tsum hsum]
  rw [hsplit] at hone
  have htail' := mul_le_mul_of_nonneg_left htail hN
  change N * (∑' i, tail i) ≤ N * (1 / 4) at htail'
  linarith

end BakerHarman
