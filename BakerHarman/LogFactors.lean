import BakerHarman.ExponentialSum

/-!
# Absorbing logarithmic factors in the analytic estimates

Gaussian detection uses a logarithmic frequency radius. Fixed powers of
`log R + 1` can be absorbed in the same numerator-exponent margin already used
for fixed factors, while retaining saving `23 * gammaBH K / 20`.
-/

namespace BakerHarman

open OAI.Problem337

/-- Any fixed multiple of a fixed power of `log R + 1` is eventually bounded
by any positive power of `R`. -/
theorem log_add_one_pow_absorbed (C ε : ℝ) (n : ℕ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in Filter.atTop, C * (Real.log R + 1) ^ n ≤ R ^ ε := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (n : ℝ) hε).const_mul_left
    (|C| * (2 : ℝ) ^ n)
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_ge_atTop (1 : ℝ)] with R hbound hlog hR
  have hR0 : 0 < R := by linarith
  have hlog0 : 0 ≤ Real.log R := by linarith
  simp only [Real.rpow_natCast, Real.norm_eq_abs, one_mul] at hbound
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (Real.rpow_nonneg hR0.le _)] at hbound
  have hp : (Real.log R + 1) ^ n ≤ (2 * Real.log R) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  calc
    _ ≤ |C| * (Real.log R + 1) ^ n :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 * Real.log R) ^ n := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    _ = (|C| * (2 : ℝ) ^ n) * (Real.log R) ^ n := by rw [mul_pow]; ring
    _ ≤ _ := hbound

/-- Reciprocal-sum estimate allowing any fixed logarithmic factor in the
numerator range. Its constant depends only on `K`; the threshold for `R` also
depends on the multiplier and logarithmic degree. -/
theorem bakerHarman_reciprocal_sum_log_factor (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (n : ℕ),
      ∀ᶠ R : ℝ in Filter.atTop, ∀ (Z : ℝ) (L U : ℤ),
        Z ≠ 0 → |Z| ≤ B * (Real.log R + 1) ^ n * R ^ (K + 1) →
        R ≤ L → (U : ℝ) ≤ 2 * R →
        ‖∑ r ∈ Finset.Icc L U, differencingPhase (Z / r)‖ ≤
          C * (R ^ (1 - (23 / 20 : ℝ) * gammaBH K) + R ^ 2 / |Z|) := by
  obtain ⟨K', hKK', hmargin⟩ := exists_analyticSaving_margin K
  obtain ⟨C, hC, hbound⟩ := bakerHarman_reciprocal_sum K' (hK.trans hKK'.le)
  refine ⟨C, hC, fun B n => ?_⟩
  filter_upwards [log_add_one_pow_absorbed B (K' - K) n (sub_pos.mpr hKK'),
    Filter.eventually_ge_atTop (1 : ℝ)] with R hgrow hR
  intro Z L U hZ hZupper hL hU
  have hR0 : 0 < R := by linarith
  have hu : |Z| ≤ R ^ (K' + 1) := by
    calc
      _ ≤ B * (Real.log R + 1) ^ n * R ^ (K + 1) := hZupper
      _ ≤ R ^ (K' - K) * R ^ (K + 1) :=
        mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hR0.le _)
      _ = R ^ (K' + 1) := by rw [← Real.rpow_add hR0]; congr 1; ring
  have h := hbound R Z L U hR hZ hu hL hU
  have hp : R ^ (1 - analyticSaving K') ≤ R ^ (1 - (23 / 20 : ℝ) * gammaBH K) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) hC.le)

end BakerHarman
