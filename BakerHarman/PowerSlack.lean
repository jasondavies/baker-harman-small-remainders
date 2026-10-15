import BakerHarman.LogFactors

/-!
# Analytic power slack

The retained saving `23γ/20` still absorbs the cutoff at power range `26γ/25`:
`23/20 - (11/10)(26/25) = 3/500`. This strict margin permits dimension
induction with the paper's logarithmic degrees.
-/

namespace BakerHarman

/-- A power range slightly beyond `gammaBH`, funded by the retained analytic saving. -/
noncomputable def analyticPowerRange (K : ℝ) : ℝ := (26 / 25 : ℝ) * gammaBH K

lemma analyticPowerRange_pos (K : ℝ) : 0 < analyticPowerRange K := by
  unfold analyticPowerRange
  positivity [gammaBH_pos K]

lemma gammaBH_lt_analyticPowerRange (K : ℝ) : gammaBH K < analyticPowerRange K := by
  unfold analyticPowerRange
  nlinarith [gammaBH_pos K]

lemma analyticPowerRange_le_one (K : ℝ) : analyticPowerRange K ≤ 1 := by
  unfold analyticPowerRange
  linarith [gammaBH_le K]

open OAI.Problem337

/-- Absorb the power term after allowing fixed factors in the numerator range. -/
theorem bakerHarman_slack_power_absorbed (K C : ℝ) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ Q : ℝ, 0 < Q → Q ≤ R ^ analyticPowerRange K →
      C * R ^ (1 - (23 / 20 : ℝ) * gammaBH K) ≤
        R * Q ^ (-(11 / 10 : ℝ)) / 2 := by
  have hgap : 0 < 3 * gammaBH K / 500 := by positivity [gammaBH_pos K]
  have hgrow : ∀ᶠ R : ℝ in Filter.atTop, 2 * C ≤ R ^ (3 * gammaBH K / 500) :=
    (tendsto_rpow_atTop hgap).eventually (Filter.eventually_ge_atTop (2 * C))
  filter_upwards [hgrow, Filter.eventually_ge_atTop (1 : ℝ)] with R hgrow hR
  intro Q hQ hQR
  have hR0 : 0 < R := by linarith
  have hcut : R ^ (1 - (11 / 10 : ℝ) * analyticPowerRange K) ≤ R * Q ^ (-(11 / 10 : ℝ)) := by
    calc
      _ = R * (R ^ analyticPowerRange K) ^ (-(11 / 10 : ℝ)) := by
        rw [← Real.rpow_mul hR0.le]
        conv_rhs => lhs; rw [← Real.rpow_one R]
        rw [← Real.rpow_add hR0]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hQ hQR (by norm_num)) hR0.le
  have hmul := mul_le_mul_of_nonneg_right hgrow
    (Real.rpow_nonneg hR0.le (1 - (23 / 20 : ℝ) * gammaBH K))
  have hid : R ^ (3 * gammaBH K / 500) * R ^ (1 - (23 / 20 : ℝ) * gammaBH K) =
      R ^ (1 - (11 / 10 : ℝ) * analyticPowerRange K) := by
    rw [← Real.rpow_add hR0]
    congr 1
    unfold analyticPowerRange
    ring
  rw [hid] at hmul
  nlinarith

/-- A sum of size at least `T`, above the small-sum cutoff, has numerator
at most a constant times `R²/T`. Fixed logarithmic factors are permitted in
the numerator range. The bound includes the zero numerator. -/
theorem bakerHarman_slack_large_sum_frequency_log_factor (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (n : ℕ),
      ∀ᶠ R : ℝ in Filter.atTop, ∀ (Q Z T : ℝ) (L U : ℤ),
        0 < Q → Q ≤ R ^ analyticPowerRange K → |Z| ≤ B * (Real.log R + 1) ^ n * R ^ (K + 1) →
        R ≤ L → (U : ℝ) ≤ 2 * R → R * Q ^ (-(11 / 10 : ℝ)) ≤ T →
        T ≤ ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ →
        |Z| ≤ C * R ^ 2 / T := by
  obtain ⟨C, hC, hbound⟩ := bakerHarman_reciprocal_sum_log_factor K hK
  refine ⟨2 * C, by positivity, fun B n => ?_⟩
  filter_upwards [hbound B n, bakerHarman_slack_power_absorbed K C,
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
theorem bakerHarman_slack_large_sum_frequency (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ,
      ∀ᶠ R : ℝ in Filter.atTop, ∀ (Q Z T : ℝ) (L U : ℤ),
        0 < Q → Q ≤ R ^ analyticPowerRange K → |Z| ≤ B * R ^ (K + 1) →
        R ≤ L → (U : ℝ) ≤ 2 * R → R * Q ^ (-(11 / 10 : ℝ)) ≤ T →
        T ≤ ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ →
        |Z| ≤ C * R ^ 2 / T := by
  obtain ⟨C, hC, hbound⟩ := bakerHarman_slack_large_sum_frequency_log_factor K hK
  exact ⟨C, hC, fun B => by simpa only [pow_zero, mul_one] using hbound B 0⟩

end BakerHarman
