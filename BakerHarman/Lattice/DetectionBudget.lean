import BakerHarman.Lattice.FourierDetection

/-!
# Logarithmic parameters for Gaussian detection

The temperature and dual radius can both be chosen proportional to `log Q + 1`.
This makes the spatial and spectral tail exponents identical. A power estimate
then absorbs the Gaussian normalizer uniformly over separated lattices of
covolume at most `Q`.
-/

namespace BakerHarman

noncomputable def detectionTemperature (d : ℕ) (Q : ℝ) : ℝ :=
  8 * ((d : ℝ) + 1) * (Real.log Q + 1)

lemma detectionTemperature_lower (d : ℕ) (Q : ℝ) (hQ : 1 ≤ Q) :
    8 * ((d : ℝ) + 1) ≤ detectionTemperature d Q := by
  have hlog := Real.log_nonneg hQ
  unfold detectionTemperature
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) hlog]

/-- The Gaussian tail factor times its normalizer is at most `1/4` for large
`Q`. The threshold depends only on the dimension. -/
theorem detectionTemperature_budget (d : ℕ) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      Real.exp (-Real.pi * detectionTemperature d Q / 2) * (2 : ℝ) ^ d *
        (2 * (Real.sqrt (detectionTemperature d Q)) ^ d * Q) ≤ 1 / 4 := by
  let a : ℝ := 8 * ((d : ℝ) + 1)
  let C : ℝ := 2 * (2 : ℝ) ^ d * a ^ d
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), Filter.eventually_ge_atTop (4 * C)] with Q hQ hQC
  have hQ0 : 0 < Q := by linarith
  have hlog : 0 ≤ Real.log Q := Real.log_nonneg hQ
  let t := detectionTemperature d Q
  have htlow : a ≤ t := detectionTemperature_lower d Q hQ
  have ht1 : 1 ≤ t := by dsimp [a] at htlow; have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have ht0 : 0 < t := by linarith
  have htupper : t ≤ a * Q := by
    have h := Real.log_le_sub_one_of_pos hQ0
    change a * (Real.log Q + 1) ≤ a * Q
    exact mul_le_mul_of_nonneg_left (by linarith) ha.le
  have hsqrt : Real.sqrt t ≤ a * Q := by
    have hself : Real.sqrt t ≤ t := by
      nlinarith [Real.sq_sqrt ht0.le, Real.sqrt_nonneg t]
    exact hself.trans htupper
  have hpower : (Real.sqrt t) ^ d ≤ a ^ d * Q ^ d := by
    simpa only [mul_pow] using pow_le_pow_left₀ (Real.sqrt_nonneg t) hsqrt d
  have hexponent : -Real.pi * t / 2 ≤ Real.log Q * (-((d + 2 : ℕ) : ℝ)) := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hpit := mul_nonneg (sub_nonneg.mpr hpi) ht0.le
    have hdl := mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hlog
    dsimp [t, detectionTemperature] at *
    push_cast
    nlinarith
  have hexp : Real.exp (-Real.pi * t / 2) ≤ Q ^ (-((d + 2 : ℕ) : ℝ)) := by
    rw [Real.rpow_def_of_pos hQ0]
    exact Real.exp_le_exp.mpr hexponent
  have hcombine : Q ^ (-((d + 2 : ℕ) : ℝ)) * Q ^ (d + 1) = Q⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hQ0]
    have he : -((d + 2 : ℕ) : ℝ) + ((d + 1 : ℕ) : ℝ) = -1 := by push_cast; ring
    rw [he, Real.rpow_neg_one]
  have hbound : Real.exp (-Real.pi * t / 2) * (2 : ℝ) ^ d *
      (2 * (Real.sqrt t) ^ d * Q) ≤ C / Q := by
    calc
      _ ≤ Q ^ (-((d + 2 : ℕ) : ℝ)) * (2 : ℝ) ^ d * (2 * (a ^ d * Q ^ d) * Q) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hexp (by positivity))
          (by nlinarith [mul_le_mul_of_nonneg_right hpower hQ0.le]) (by positivity) (by positivity)
      _ = C * (Q ^ (-((d + 2 : ℕ) : ℝ)) * Q ^ (d + 1)) := by dsimp [C]; rw [pow_succ]; ring
      _ = C / Q := by rw [hcombine, div_eq_mul_inv]
  exact hbound.trans ((div_le_iff₀ hQ0).mpr (by linarith))

open OAI.Erdos3 Classical

/-- Uniform Fourier detection with logarithmic dual radius. The threshold for
`Q` depends only on the dimension, before choosing the ambient space, lattice,
or sequence. The finite set of detected
frequencies has at most a constant times `Q (log Q + 1)^dimension` elements. -/
theorem gaussian_lattice_detection (d : ℕ) :
    ∀ᶠ Q : ℝ in Filter.atTop, ∀ (E : Type*)
      [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E], Module.finrank ℝ E = d → ∀ (Λ : Submodule ℤ E)
      [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖) → ZLattice.covolume Λ ≤ Q →
      ∀ (ι : Type*) (s : Finset ι) (x : ι → E),
      (∀ i ∈ s, ∀ m : Λ, 1 ≤ ‖x i - (m : E)‖) →
      ((dualBall Λ (detectionTemperature d Q)).card : ℝ) ≤
        (2 * Real.exp Real.pi * (8 * ((d : ℝ) + 1)) ^ d) * Q * (Real.log Q + 1) ^ d ∧
      (s.card : ℝ) / 4 ≤ ∑ ξ ∈ (dualBall Λ (detectionTemperature d Q)).erase 0,
        ‖∑ i ∈ s, euclideanCharacter (ξ : E) (x i)‖ := by
  filter_upwards [detectionTemperature_budget d,
    Filter.eventually_ge_atTop (1 : ℝ)] with Q hbudget hQ
  intro E _ _ _ _ _ hdim Λ _ _ hsep hcov ι s x hfar
  let t := detectionTemperature d Q
  have htlow : 8 * ((d : ℝ) + 1) ≤ t := detectionTemperature_lower d Q hQ
  have ht1 : 1 ≤ t := by have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have ht : 0 < t := by linarith
  have hmass : normalizedLatticeGaussian Λ t 0 ≤ 2 * (Real.sqrt t) ^ d * Q := by
    have h := latticeGaussianMass_le_two_of_separated Λ t (by simpa only [hdim] using htlow) hsep
    have hp := mul_le_mul_of_nonneg_left h (latticeGaussianNormalizer_nonneg Λ t)
    have hq := mul_le_mul_of_nonneg_left hcov (show 0 ≤ 2 * (Real.sqrt t) ^ d by positivity)
    unfold latticeGaussianNormalizer at hp
    unfold normalizedLatticeGaussian latticeGaussianNormalizer
    rw [hdim] at hp ⊢
    nlinarith only [hp, hq]
  have hsmall : Real.exp (-Real.pi * t / 2) * (2 : ℝ) ^ d *
      normalizedLatticeGaussian Λ t 0 ≤ 1 / 4 := by
    exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans hbudget
  constructor
  · have ht2 : 8 * ((d : ℝ) + 1) ≤ t ^ 2 := by nlinarith
    have h := dual_card_le_of_separated Λ t ht (by simpa only [hdim] using ht2) hsep (dualBall Λ t)
      (fun ξ hξ => (mem_dualBall Λ t ξ).mp hξ)
    have hq := mul_le_mul_of_nonneg_left hcov
      (show 0 ≤ 2 * Real.exp Real.pi * t ^ d by positivity)
    rw [hdim] at h
    have hbound := h.trans hq
    convert hbound using 1
    dsimp [t, detectionTemperature]
    simp only [mul_pow]
    ring
  · apply lattice_fourier_detection Λ s x t t ht ht.le hfar
      (by rw [hdim]; linarith only [hsmall])
    have he : -Real.pi / t * t ^ 2 / 2 = -Real.pi * t / 2 := by field_simp
    rwa [he, hdim]

end BakerHarman
