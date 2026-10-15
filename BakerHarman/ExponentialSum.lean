import BakerHarman.BandSelection

/-!
# Reciprocal exponential sums throughout the Baker–Harman range

The small-numerator estimate and the finite chain of derivative bands give one
bound with saving `analyticSaving K = (6/5) * gammaBH K`. All constants are
uniform in the numerator and in closed integer subintervals of `[R,2R]`.
-/

namespace BakerHarman

open OAI.Problem337

/-- The reciprocal exponential-sum estimate needed by the lattice argument,
with a power saving strictly larger than the desired range exponent. -/
theorem bakerHarman_reciprocal_sum (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Z : ℝ) (L U : ℤ),
      1 ≤ R → Z ≠ 0 → |Z| ≤ R ^ (K + 1) → R ≤ L → (U : ℝ) ≤ 2 * R →
      ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤
        C * (R ^ (1 - analyticSaving K) + R ^ 2 / |Z|) := by
  obtain ⟨m, hlo, hhi, hoverlap⟩ := exists_bakerHarman_band_cover K hK
  obtain ⟨C, hC, hbound⟩ := reciprocal_sum_finite_bands m
  refine ⟨253 + C, by positivity, ?_⟩
  intro R Z L U hR hZ hZupper hL hU
  have hR0 : 0 < R := by linarith
  have hp : 0 ≤ R ^ (1 - analyticSaving K) := Real.rpow_nonneg hR0.le _
  have hrecip : 0 ≤ R ^ 2 / |Z| := div_nonneg (sq_nonneg R) (abs_nonneg Z)
  by_cases hsmall : |Z| ≤ R ^ 2
  · have h := reciprocal_sum_base_order_int R Z L U hR hZ hsmall hL hU
    change ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤ _ at h
    have hsqrt : Real.sqrt R ≤ R ^ (1 - analyticSaving K) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hR (by linarith [(analyticSaving_bounds K).2])
    nlinarith [mul_nonneg hC.le (add_nonneg hp hrecip)]
  · have hlower : R ^ derivativeBandLower 0 (analyticSaving K) ≤ |Z| := by
      calc
        _ ≤ R ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR hlo
        _ = R ^ (2 : ℕ) := by norm_num
        _ ≤ |Z| := (not_le.mp hsmall).le
    have hupper : |Z| ≤ R ^ derivativeBandUpper m (analyticSaving K) :=
      hZupper.trans (Real.rpow_le_rpow_of_exponent_le hR hhi)
    have h := hbound (analyticSaving K) R Z L U hR hlower hupper hoverlap hL hU
    nlinarith [mul_nonneg hC.le hrecip]

/-- A slightly larger numerator exponent still leaves saving `23γ/20`.
This absorbs any fixed factor in the numerator range as `R` tends to infinity. -/
lemma exists_analyticSaving_margin (K : ℝ) :
    ∃ K' : ℝ, K < K' ∧ (23 / 20 : ℝ) * gammaBH K < analyticSaving K' := by
  have hc : Continuous analyticSaving := continuous_const.mul gammaBH_continuous
  have hm : (23 / 20 : ℝ) * gammaBH K < analyticSaving K := by
    unfold analyticSaving
    nlinarith [gammaBH_pos K]
  have he : ∀ᶠ x in nhds K, (23 / 20 : ℝ) * gammaBH K < analyticSaving x :=
    hc.continuousAt.eventually (lt_mem_nhds hm)
  obtain ⟨a, b, hab, hsub⟩ := he.exists_Ioo_subset
  obtain ⟨K', hKK', hK'b⟩ := exists_between hab.2
  exact ⟨K', hKK', hsub ⟨hab.1.trans hKK', hK'b⟩⟩

/-- Uniform estimate allowing a fixed multiplier in the numerator range.
The estimate's constant depends only on `K`; the threshold for `R` may also
depend on the multiplier `B`. -/
theorem bakerHarman_reciprocal_sum_fixed_factor (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ,
      ∀ᶠ R : ℝ in Filter.atTop, ∀ (Z : ℝ) (L U : ℤ),
        Z ≠ 0 → |Z| ≤ B * R ^ (K + 1) → R ≤ L → (U : ℝ) ≤ 2 * R →
        ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤
          C * (R ^ (1 - (23 / 20 : ℝ) * gammaBH K) + R ^ 2 / |Z|) := by
  obtain ⟨K', hKK', hmargin⟩ := exists_analyticSaving_margin K
  obtain ⟨C, hC, hbound⟩ := bakerHarman_reciprocal_sum K' (hK.trans hKK'.le)
  refine ⟨C, hC, fun B => ?_⟩
  have hgrow : ∀ᶠ R : ℝ in Filter.atTop, B ≤ R ^ (K' - K) :=
    (tendsto_rpow_atTop (sub_pos.mpr hKK')).eventually (Filter.eventually_ge_atTop B)
  filter_upwards [hgrow, Filter.eventually_ge_atTop (1 : ℝ)] with R hgrow hR
  intro Z L U hZ hZupper hL hU
  have hR0 : 0 < R := by linarith
  have hu : |Z| ≤ R ^ (K' + 1) := by
    calc
      _ ≤ B * R ^ (K + 1) := hZupper
      _ ≤ R ^ (K' - K) * R ^ (K + 1) :=
        mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hR0.le _)
      _ = R ^ (K' + 1) := by rw [← Real.rpow_add hR0]; congr 1; ring
  have h := hbound R Z L U hR hZ hu hL hU
  have hp : R ^ (1 - analyticSaving K') ≤ R ^ (1 - (23 / 20 : ℝ) * gammaBH K) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hp le_rfl) hC.le)

end BakerHarman
