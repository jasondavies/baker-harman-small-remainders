import BakerHarman.HigherDerivative

/-!
# Numerator bands for reciprocal exponential sums

Apply a fixed derivative order to `R^lo ≤ |Z| ≤ R^hi`, exposing both resulting
powers of `R`. These bounds are the input to the finite-order selection needed
for the Baker–Harman range `|Z| ≤ R^(K+1)`.
-/

open scoped BigOperators
open OAI.Problem337

namespace BakerHarman

/-- Both powers of `R` furnished by a fixed derivative order on a numerator
band. The constant depends only on the order, not on the band or its endpoints. -/
theorem reciprocal_sum_power_band (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Z lo hi : ℝ) (L U : ℤ),
      1 ≤ R → R ^ lo ≤ |Z| → |Z| ≤ R ^ hi → R ≤ L → (U : ℝ) ≤ 2 * R →
      ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤
        C * (R ^ (1 + (hi - (r + 3 : ℕ)) * derivativeMainExponent r) +
          R ^ (1 - 2 * derivativeErrorExponent r +
            ((r + 3 : ℕ) - lo) * derivativeErrorExponent r)) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_sum_higher_derivative_uniform r
  refine ⟨C, hC, ?_⟩
  intro R Z lo hi L U hR hlo hhi hL hU
  have hR0 : 0 < R := by linarith
  have hZ : Z ≠ 0 := abs_pos.mp ((Real.rpow_pos_of_pos hR0 lo).trans_le hlo)
  have h := hbound R Z L U hR hZ hL hU
  have hmu0 : 0 < |Z| / R ^ (r + 3) := div_pos (abs_pos.mpr hZ) (pow_pos hR0 _)
  have hlower : R ^ (lo - (r + 3 : ℕ)) ≤ |Z| / R ^ (r + 3) := by
    rw [Real.rpow_sub hR0, Real.rpow_natCast]
    exact div_le_div_of_nonneg_right hlo (by positivity)
  have hupper : |Z| / R ^ (r + 3) ≤ R ^ (hi - (r + 3 : ℕ)) := by
    rw [Real.rpow_sub hR0, Real.rpow_natCast]
    exact div_le_div_of_nonneg_right hhi (by positivity)
  have ha := (derivativeMainExponent_bounds r).1
  have hc := derivativeErrorExponent_pos r
  have hmain : R * (|Z| / R ^ (r + 3)) ^ derivativeMainExponent r ≤
      R ^ (1 + (hi - (r + 3 : ℕ)) * derivativeMainExponent r) := by
    calc
      _ ≤ R * (R ^ (hi - (r + 3 : ℕ))) ^ derivativeMainExponent r :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hmu0.le hupper ha.le) hR0.le
      _ = _ := by
        rw [← Real.rpow_mul hR0.le]
        conv_lhs => lhs; rw [← Real.rpow_one R]
        rw [← Real.rpow_add hR0]
  have herror : R ^ (1 - 2 * derivativeErrorExponent r) *
      (|Z| / R ^ (r + 3)) ^ (-derivativeErrorExponent r) ≤
      R ^ (1 - 2 * derivativeErrorExponent r +
        ((r + 3 : ℕ) - lo) * derivativeErrorExponent r) := by
    calc
      _ ≤ R ^ (1 - 2 * derivativeErrorExponent r) *
          (R ^ (lo - (r + 3 : ℕ))) ^ (-derivativeErrorExponent r) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hR0 _) hlower (by linarith))
          (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul hR0.le, ← Real.rpow_add hR0]
        congr 1
        ring
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hmain herror) hC.le)

/-- Lower numerator exponent for which this order delivers saving `δ`. -/
noncomputable def derivativeBandLower (r : ℕ) (δ : ℝ) : ℝ :=
  (r + 1 : ℕ) + (2 : ℝ) ^ (r + 1) * δ

/-- Upper numerator exponent for which this order delivers saving `δ`. -/
noncomputable def derivativeBandUpper (r : ℕ) (δ : ℝ) : ℝ :=
  (r + 3 : ℕ) - ((2 : ℝ) ^ (r + 2) - 2) * δ

/-- A fixed derivative order gives the requested power saving throughout its
explicit numerator band. The constant is uniform in the requested saving. -/
theorem reciprocal_sum_band_saving (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ R Z : ℝ) (L U : ℤ),
      1 ≤ R → R ^ derivativeBandLower r δ ≤ |Z| →
      |Z| ≤ R ^ derivativeBandUpper r δ → R ≤ L → (U : ℝ) ≤ 2 * R →
      ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤ C * R ^ (1 - δ) := by
  obtain ⟨C, hC, hbound⟩ := reciprocal_sum_power_band r
  refine ⟨2 * C, by positivity, ?_⟩
  intro δ R Z L U hR hlo hhi hL hU
  have h := hbound R Z (derivativeBandLower r δ) (derivativeBandUpper r δ) L U hR hlo hhi hL hU
  have hden : (2 : ℝ) ^ (r + 2) - 2 ≠ 0 := by
    have hpos := (derivativeMainExponent_bounds r).1
    intro h
    simp [derivativeMainExponent, h] at hpos
  have hmain : 1 + (derivativeBandUpper r δ - (r + 3 : ℕ)) * derivativeMainExponent r = 1 - δ := by
    unfold derivativeBandUpper derivativeMainExponent
    field_simp
    ring
  have herror : 1 - 2 * derivativeErrorExponent r +
      ((r + 3 : ℕ) - derivativeBandLower r δ) * derivativeErrorExponent r = 1 - δ := by
    unfold derivativeBandLower derivativeErrorExponent
    push_cast
    field_simp
    ring
  rw [hmain, herror] at h
  nlinarith only [h]

/-- Neighboring derivative bands overlap whenever the saving is below this
explicit threshold. This is the numerical condition for finite-order coverage. -/
lemma derivativeBand_overlap (r : ℕ) (δ : ℝ)
    (hδ : ((2 : ℝ) ^ (r + 3) - 2) * δ ≤ 1) :
    derivativeBandLower (r + 1) δ ≤ derivativeBandUpper r δ := by
  unfold derivativeBandLower derivativeBandUpper
  push_cast
  simp only [pow_succ] at hδ ⊢
  nlinarith only [hδ]

/-- A finite chain of overlapping bands gives one uniform constant for their
entire covered range. Later order selection need only verify the endpoints and
the overlap inequalities; it does not need to manipulate exponential sums. -/
theorem reciprocal_sum_finite_bands (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ R Z : ℝ) (L U : ℤ),
      1 ≤ R → R ^ derivativeBandLower 0 δ ≤ |Z| →
      |Z| ≤ R ^ derivativeBandUpper m δ →
      (∀ r < m, ((2 : ℝ) ^ (r + 3) - 2) * δ ≤ 1) →
      R ≤ L → (U : ℝ) ≤ 2 * R →
      ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤ C * R ^ (1 - δ) := by
  induction m with
  | zero =>
    obtain ⟨C, hC, hbound⟩ := reciprocal_sum_band_saving 0
    exact ⟨C, hC, fun δ R Z L U hR hlo hhi _ hL hU => hbound δ R Z L U hR hlo hhi hL hU⟩
  | succ m ih =>
    obtain ⟨C₀, hC₀, hbound₀⟩ := ih
    obtain ⟨C₁, hC₁, hbound₁⟩ := reciprocal_sum_band_saving (m + 1)
    refine ⟨C₀ + C₁, by positivity, ?_⟩
    intro δ R Z L U hR hlo hhi hoverlap hL hU
    have hpow : 0 ≤ R ^ (1 - δ) := Real.rpow_nonneg (by linarith) _
    by_cases hprev : |Z| ≤ R ^ derivativeBandUpper m δ
    · have h := hbound₀ δ R Z L U hR hlo hprev
        (fun r hr => hoverlap r (by omega)) hL hU
      nlinarith [mul_nonneg hC₁.le hpow]
    · have hlow : R ^ derivativeBandLower (m + 1) δ ≤ |Z| := by
        calc
          _ ≤ R ^ derivativeBandUpper m δ := Real.rpow_le_rpow_of_exponent_le hR
            (derivativeBand_overlap m δ (hoverlap m (by omega)))
          _ ≤ |Z| := (not_le.mp hprev).le
      have h := hbound₁ δ R Z L U hR hlow hhi hL hU
      nlinarith [mul_nonneg hC₀.le hpow]

end BakerHarman
