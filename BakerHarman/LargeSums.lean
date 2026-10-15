import BakerHarman.LogFactors

/-!
# Frequencies with large reciprocal sums

With cutoff `R Q^(-11/10)`, the fixed-factor exponential-sum estimate leaves
a positive power gap `gammaBH K / 20`. Thus the reciprocal term controls every
sum above the cutoff, uniformly for `Q ≤ R^gammaBH K`.
-/

namespace BakerHarman

open OAI.Problem337

/-- Absorb the power term after allowing fixed factors in the numerator range. -/
theorem bakerHarman_analytic_power_absorbed (K C : ℝ) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ Q : ℝ, 0 < Q → Q ≤ R ^ gammaBH K →
      C * R ^ (1 - (23 / 20 : ℝ) * gammaBH K) ≤
        R * Q ^ (-(11 / 10 : ℝ)) / 2 := by
  have hgap : 0 < gammaBH K / 20 := div_pos (gammaBH_pos K) (by norm_num)
  have hgrow : ∀ᶠ R : ℝ in Filter.atTop, 2 * C ≤ R ^ (gammaBH K / 20) :=
    (tendsto_rpow_atTop hgap).eventually (Filter.eventually_ge_atTop (2 * C))
  filter_upwards [hgrow, Filter.eventually_ge_atTop (1 : ℝ)] with R hgrow hR
  intro Q hQ hQR
  have hR0 : 0 < R := by linarith
  have hcut : R ^ (1 - (11 / 10 : ℝ) * gammaBH K) ≤ R * Q ^ (-(11 / 10 : ℝ)) := by
    calc
      _ = R * (R ^ gammaBH K) ^ (-(11 / 10 : ℝ)) := by
        rw [← Real.rpow_mul hR0.le]
        conv_rhs => lhs; rw [← Real.rpow_one R]
        rw [← Real.rpow_add hR0]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hQ hQR (by norm_num)) hR0.le
  have hmul := mul_le_mul_of_nonneg_right hgrow
    (Real.rpow_nonneg hR0.le (1 - (23 / 20 : ℝ) * gammaBH K))
  have hid : R ^ (gammaBH K / 20) * R ^ (1 - (23 / 20 : ℝ) * gammaBH K) =
      R ^ (1 - (11 / 10 : ℝ) * gammaBH K) := by
    rw [← Real.rpow_add hR0]
    congr 1
    ring
  rw [hid] at hmul
  nlinarith

/-- A sum of size at least `T`, above the small-sum cutoff, has numerator
at most a constant times `R²/T`. Fixed logarithmic factors are permitted in
the numerator range. The bound includes the zero numerator. -/
theorem bakerHarman_large_sum_frequency_log_factor (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (n : ℕ),
      ∀ᶠ R : ℝ in Filter.atTop, ∀ (Q Z T : ℝ) (L U : ℤ),
        0 < Q → Q ≤ R ^ gammaBH K → |Z| ≤ B * (Real.log R + 1) ^ n * R ^ (K + 1) →
        R ≤ L → (U : ℝ) ≤ 2 * R → R * Q ^ (-(11 / 10 : ℝ)) ≤ T →
        T ≤ ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ →
        |Z| ≤ C * R ^ 2 / T := by
  obtain ⟨C, hC, hbound⟩ := bakerHarman_reciprocal_sum_log_factor K hK
  refine ⟨2 * C, by positivity, fun B n => ?_⟩
  filter_upwards [hbound B n, bakerHarman_analytic_power_absorbed K C,
    Filter.eventually_ge_atTop (1 : ℝ)] with R hbound habsorb hR
  intro Q Z T L U hQ hQR hZupper hL hU hcut hlarge
  have hR0 : 0 < R := by linarith
  have hT : 0 < T := lt_of_lt_of_le (mul_pos hR0 (Real.rpow_pos_of_pos hQ _)) hcut
  by_cases hZ : Z = 0
  · rw [hZ, abs_zero]
    positivity
  have h := hlarge.trans (hbound Z L U hZ hZupper hL hU)
  have hp := habsorb Q hQ hQR
  have hrecip : T ≤ 2 * C * R ^ 2 / |Z| := by
    simp only [div_eq_mul_inv] at h hp ⊢
    nlinarith
  have hm := (le_div_iff₀ (abs_pos.mpr hZ)).mp hrecip
  exact (le_div_iff₀ hT).mpr (by nlinarith only [hm])

/-- Fixed-factor version of the large-sum frequency bound. -/
theorem bakerHarman_large_sum_frequency (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ,
      ∀ᶠ R : ℝ in Filter.atTop, ∀ (Q Z T : ℝ) (L U : ℤ),
        0 < Q → Q ≤ R ^ gammaBH K → |Z| ≤ B * R ^ (K + 1) →
        R ≤ L → (U : ℝ) ≤ 2 * R → R * Q ^ (-(11 / 10 : ℝ)) ≤ T →
        T ≤ ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ →
        |Z| ≤ C * R ^ 2 / T := by
  obtain ⟨C, hC, hbound⟩ := bakerHarman_large_sum_frequency_log_factor K hK
  exact ⟨C, hC, fun B => by simpa only [pow_zero, mul_one] using hbound B 0⟩

end BakerHarman
