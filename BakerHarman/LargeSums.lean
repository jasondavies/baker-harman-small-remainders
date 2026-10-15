import BakerHarman.PowerSlack

/-!
# Frequencies with large reciprocal sums

With cutoff `R Q^(-11/10)`, the fixed-factor exponential-sum estimate leaves
a positive power gap `gammaBH K / 20`. Thus the reciprocal term controls every
sum above the cutoff, uniformly for `Q ≤ R^gammaBH K`. The proofs specialize
the wider power range in `PowerSlack`.
-/

namespace BakerHarman

open OAI.Problem337

/-- Absorb the power term after allowing fixed factors in the numerator range. -/
theorem bakerHarman_analytic_power_absorbed (K C : ℝ) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ Q : ℝ, 0 < Q → Q ≤ R ^ gammaBH K →
      C * R ^ (1 - (23 / 20 : ℝ) * gammaBH K) ≤
        R * Q ^ (-(11 / 10 : ℝ)) / 2 := by
  filter_upwards [bakerHarman_slack_power_absorbed K C,
    Filter.eventually_ge_atTop (1 : ℝ)] with R h hR
  intro Q hQ hQR
  exact h Q hQ (hQR.trans (Real.rpow_le_rpow_of_exponent_le hR
    (gammaBH_lt_analyticPowerRange K).le))

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
  obtain ⟨C, hC, h⟩ := bakerHarman_slack_large_sum_frequency_log_factor K hK
  refine ⟨C, hC, fun B n => ?_⟩
  filter_upwards [h B n, Filter.eventually_ge_atTop (1 : ℝ)] with R h hR
  intro Q Z T L U hQ hQR
  exact h Q Z T L U hQ (hQR.trans (Real.rpow_le_rpow_of_exponent_le hR
    (gammaBH_lt_analyticPowerRange K).le))

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
