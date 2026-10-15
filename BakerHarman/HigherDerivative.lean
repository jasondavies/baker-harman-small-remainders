import BakerHarman.DifferencingBudget

/-!
# Higher-order reciprocal exponential-sum estimates

The optimized A-process is iterated with explicit main and error exponents.
The total derivative order is fixed as each step adds a forward difference.
-/

open scoped BigOperators
open OAI.Problem337

namespace BakerHarman

noncomputable def derivativeMainExponent (r : ℕ) : ℝ := 1 / ((2 : ℝ) ^ (r + 2) - 2)

noncomputable def derivativeErrorExponent (r : ℕ) : ℝ := 1 / (2 : ℝ) ^ (r + 1)

noncomputable def derivativeBoundConstant (D : ℕ) : ℕ → ℝ
  | 0 => 2 * (6 * (3 : ℝ) ^ (D + 1) + 15)
  | r + 1 => 4 * (derivativeBoundConstant D r + 1)

lemma derivativeBoundConstant_nonneg (D r : ℕ) : 0 ≤ derivativeBoundConstant D r := by
  induction r with
  | zero => dsimp [derivativeBoundConstant]; positivity
  | succ r ih => dsimp [derivativeBoundConstant]; positivity

lemma derivativeMainExponent_bounds (r : ℕ) :
    0 < derivativeMainExponent r ∧ derivativeMainExponent r ≤ 1 / 2 := by
  have hp : (4 : ℝ) ≤ 2 ^ (r + 2) := by
    calc
      (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ 2 ^ (r + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold derivativeMainExponent
  constructor
  · exact one_div_pos.mpr (by linarith)
  · exact one_div_le_one_div_of_le (by norm_num) (by linarith)

lemma derivativeErrorExponent_pos (r : ℕ) : 0 < derivativeErrorExponent r := by
  unfold derivativeErrorExponent
  positivity

lemma derivativeErrorExponent_succ (r : ℕ) :
    derivativeErrorExponent (r + 1) = derivativeErrorExponent r / 2 := by
  simp only [derivativeErrorExponent, pow_succ]
  ring

lemma derivativeMainExponent_balance (r : ℕ) :
    (1 - 2 * derivativeMainExponent (r + 1)) * derivativeMainExponent r =
      2 * derivativeMainExponent (r + 1) := by
  have hpos := (derivativeMainExponent_bounds r).1
  have hp : (2 : ℝ) ^ (r + 2) - 2 ≠ 0 := by
    intro h
    simp [derivativeMainExponent, h] at hpos
  have hp' : (2 : ℝ) ^ (r + 1 + 2) - 2 ≠ 0 := by
    have hpos' := (derivativeMainExponent_bounds (r + 1)).1
    intro h
    simp [derivativeMainExponent, h] at hpos'
  unfold derivativeMainExponent
  field_simp
  simp only [pow_succ]
  ring

lemma derivativeMainExponent_succ_le_quarter (r : ℕ) :
    derivativeMainExponent (r + 1) ≤ 1 / 4 := by
  have hp : (8 : ℝ) ≤ 2 ^ (r + 1 + 2) := by
    calc
      (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
      _ ≤ 2 ^ (r + 1 + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold derivativeMainExponent
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- The terminal estimate on integer intervals, normalized to the common
scale `R`, in the precise form used to start the induction. -/
theorem reciprocal_differenced_base_bound (D : ℕ) (R Z : ℝ) (L U : ℤ)
    (hR : 1 ≤ R) (hZ : Z ≠ 0) (hL : R ≤ L) (hU : (U : ℝ) ≤ 2 * R)
    (hs : List ℤ) (horder : hs.length + 2 = D) (hhs : ∀ h ∈ hs, 0 < h) :
    let shifts := hs.map (fun h : ℤ => (h : ℝ))
    let lam := reciprocalDerivativeScale D shifts Z R
    ‖∑ n ∈ Finset.Icc L (U - hs.sum),
      differencingPhase (forwardDifference shifts (fun y => Z / y) n)‖ ≤
      derivativeBoundConstant D 0 *
        (R * lam ^ derivativeMainExponent 0 +
          R ^ (1 - 2 * derivativeErrorExponent 0) * lam ^ (-derivativeErrorExponent 0)) := by
  dsimp only
  let shifts := hs.map (fun h : ℤ => (h : ℝ))
  let lam := reciprocalDerivativeScale D shifts Z R
  have hR0 : 0 < R := by linarith
  have hshifts : ∀ h ∈ shifts, 0 < h := by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
    exact_mod_cast hhs j hj
  have hlam : 0 < lam := reciprocalDerivativeScale_pos D shifts Z R hshifts hZ hR0
  have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun h hh => (hhs h hh).le)
  by_cases hempty : U - hs.sum < L
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    exact mul_nonneg (derivativeBoundConstant_nonneg D 0) (by positivity)
  have hne : L ≤ U - hs.sum := by omega
  let N := (U - hs.sum + 1 - L).toNat
  have hNi : (N : ℤ) = U - hs.sum + 1 - L := Int.toNat_of_nonneg (by omega)
  have hNr := congrArg (fun n : ℤ => (n : ℝ)) hNi
  simp only [Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast] at hNr
  have hsumR : shifts.sum = (hs.sum : ℝ) := by simp [shifts]
  have hsum0 : (0 : ℝ) ≤ hs.sum := by exact_mod_cast hsum
  have hN : (N : ℝ) ≤ 2 * R := by linarith
  have ht := reciprocal_differenced_second_derivative D shifts Z R L N
    (by simpa [shifts] using horder) hshifts hZ hR0 hL
    (by rw [hsumR]; linarith)
  have heq : (∑ n ∈ Finset.Icc L (U - hs.sum),
      differencingPhase (forwardDifference shifts (fun y => Z / y) n)) =
      ∑ j ∈ Finset.range N,
        differencingPhase (forwardDifference shifts (fun y => Z / y) ((j : ℝ) + L)) := by
    rw [Int.Icc_eq_finset_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
      addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast]
    rw [add_comm]
  change ‖∑ n ∈ Finset.Icc L (U - hs.sum),
      differencingPhase (forwardDifference shifts (fun y => Z / y) n)‖ ≤ _
  rw [heq]
  have hroot : lam ^ (-derivativeErrorExponent 0) = 1 / Real.sqrt lam := by
    norm_num [derivativeErrorExponent]
    rw [Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow]
  have hmain : lam ^ derivativeMainExponent 0 = Real.sqrt lam := by
    norm_num [derivativeMainExponent]
    exact (Real.sqrt_eq_rpow lam).symm
  change _ ≤ derivativeBoundConstant D 0 *
    (R * lam ^ derivativeMainExponent 0 + R ^ (1 - 2 * derivativeErrorExponent 0) *
      lam ^ (-derivativeErrorExponent 0))
  rw [hroot, hmain]
  norm_num [derivativeErrorExponent, derivativeBoundConstant]
  have hmul := mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg lam)
  have hC : 0 ≤ 6 * (3 : ℝ) ^ (D + 1) + 15 := by positivity
  have hbudget : (N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam ≤
      2 * (R * Real.sqrt lam + 1 / Real.sqrt lam) := by
    linarith [one_div_pos.mpr (Real.sqrt_pos.mpr hlam)]
  have hb := mul_le_mul_of_nonneg_left hbudget hC
  dsimp only [lam] at hb
  convert ht.trans hb using 1
  dsimp [lam]
  ring

/-- Explicit higher-derivative bound for every differenced reciprocal phase.
After `r` A-process steps the main exponent is `1/(2^(r+2)-2)` and the
error exponent is `1/2^(r+1)`. No cancellation hypothesis remains. -/
theorem reciprocal_differenced_higher_bound (r D : ℕ) (R Z : ℝ) (L U : ℤ)
    (hR : 1 ≤ R) (hZ : Z ≠ 0) (hL : R ≤ L) (hU : (U : ℝ) ≤ 2 * R) :
    ∀ hs : List ℤ, hs.length + r + 2 = D → (∀ h ∈ hs, 0 < h) →
      let shifts := hs.map (fun h : ℤ => (h : ℝ))
      let lam := reciprocalDerivativeScale D shifts Z R
      ‖∑ n ∈ Finset.Icc L (U - hs.sum),
        differencingPhase (forwardDifference shifts (fun y => Z / y) n)‖ ≤
        derivativeBoundConstant D r *
          (R * lam ^ derivativeMainExponent r +
            R ^ (1 - 2 * derivativeErrorExponent r) * lam ^ (-derivativeErrorExponent r)) := by
  induction r with
  | zero =>
    intro hs horder hhs
    exact reciprocal_differenced_base_bound D R Z L U hR hZ hL hU hs (by simpa using horder) hhs
  | succ r ih =>
    intro hs horder hhs
    dsimp only
    let shifts := hs.map (fun h : ℤ => (h : ℝ))
    let lam := reciprocalDerivativeScale D shifts Z R
    have hR0 : 0 < R := by linarith
    have hshifts : ∀ h ∈ shifts, 0 < h := by
      intro h hh
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hh
      exact_mod_cast hhs j hj
    have hlam : 0 < lam := reciprocalDerivativeScale_pos D shifts Z R hshifts hZ hR0
    by_cases hempty : U - hs.sum < L
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
      exact mul_nonneg (derivativeBoundConstant_nonneg D (r + 1)) (by positivity)
    have hne : L ≤ U - hs.sum := by omega
    let N := (U - hs.sum + 1 - L).toNat
    have hNi : (N : ℤ) = U - hs.sum + 1 - L := Int.toNat_of_nonneg (by omega)
    have hNr := congrArg (fun n : ℤ => (n : ℝ)) hNi
    simp only [Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast] at hNr
    have hsum : 0 ≤ hs.sum := List.sum_nonneg (fun h hh => (hhs h hh).le)
    have hsum0 : (0 : ℝ) ≤ hs.sum := by exact_mod_cast hsum
    have hN : (N : ℝ) ≤ 2 * R := by linarith
    have ha := derivativeMainExponent_bounds r
    have hapos := (derivativeMainExponent_bounds (r + 1)).1
    have hc := derivativeErrorExponent_pos r
    have hqhalf : 2 * derivativeMainExponent (r + 1) ≤ 1 / 2 := by
      linarith [derivativeMainExponent_succ_le_quarter r]
    have hstep := translated_interval_phase_power_step
      (forwardDifference shifts (fun y => Z / y)) L N R lam
      (derivativeMainExponent r) (derivativeErrorExponent r)
      (2 * derivativeMainExponent (r + 1)) (derivativeBoundConstant D r)
      hR hN hlam ha.1 (by linarith [ha.2]) hc.le (by positivity) hqhalf
      (derivativeMainExponent_balance r) (derivativeBoundConstant_nonneg D r) (by
        intro h hh
        have ht := ih (h :: hs) (by simp only [List.length_cons]; omega)
          (by intro j hj; rcases List.mem_cons.mp hj with rfl | hj; exact hh; exact hhs j hj)
        dsimp only at ht
        rw [List.map_cons, reciprocalDerivativeScale_cons] at ht
        have hend : L + (N : ℤ) - 1 - h = U - (h :: hs).sum := by
          simp only [List.sum_cons]
          omega
        rw [hend]
        exact ht)
    have hend : L + (N : ℤ) - 1 = U - hs.sum := by omega
    rw [hend] at hstep
    have hexp : 2 * derivativeMainExponent (r + 1) / 2 = derivativeMainExponent (r + 1) := by ring
    rw [hexp] at hstep
    change _ ≤ derivativeBoundConstant D (r + 1) *
      (R * lam ^ derivativeMainExponent (r + 1) +
        R ^ (1 - 2 * derivativeErrorExponent (r + 1)) * lam ^ (-derivativeErrorExponent (r + 1)))
    rw [derivativeBoundConstant, derivativeErrorExponent_succ]
    rw [show (1 : ℝ) - 2 * (derivativeErrorExponent r / 2) =
      1 - derivativeErrorExponent r by ring]
    simpa only [neg_div] using hstep

/-- The resulting higher-derivative estimate for the original reciprocal phase,
with no forward differences and with an explicit order-dependent constant. -/
theorem reciprocal_sum_higher_derivative (r : ℕ) (R Z : ℝ) (L U : ℤ)
    (hR : 1 ≤ R) (hZ : Z ≠ 0) (hL : R ≤ L) (hU : (U : ℝ) ≤ 2 * R) :
    let lam := ((r + 2).factorial : ℝ) * |Z| / (3 * R) ^ (r + 3)
    ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤
      derivativeBoundConstant (r + 2) r *
        (R * lam ^ derivativeMainExponent r +
          R ^ (1 - 2 * derivativeErrorExponent r) * lam ^ (-derivativeErrorExponent r)) := by
  simpa only [List.length_nil, zero_add, List.map_nil, List.sum_nil, sub_zero,
    forwardDifference, reciprocalDerivativeScale, List.prod_nil, one_mul] using
    reciprocal_differenced_higher_bound r (r + 2) R Z L U hR hZ hL hU [] (by simp) (by simp)

/-- An order-dependent constant absorbs the factorial and fixed endpoint
factors. This form exposes only `|Z| / R^(r+3)` as the derivative scale. -/
theorem reciprocal_sum_higher_derivative_uniform (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Z : ℝ) (L U : ℤ),
      1 ≤ R → Z ≠ 0 → R ≤ L → (U : ℝ) ≤ 2 * R →
      ‖∑ n ∈ Finset.Icc L U, differencingPhase (Z / n)‖ ≤
        C * (R * (|Z| / R ^ (r + 3)) ^ derivativeMainExponent r +
          R ^ (1 - 2 * derivativeErrorExponent r) *
            (|Z| / R ^ (r + 3)) ^ (-derivativeErrorExponent r)) := by
  let A : ℝ := ((r + 2).factorial : ℝ) / (3 : ℝ) ^ (r + 3)
  let D := derivativeBoundConstant (r + 2) r
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 ≤ D := derivativeBoundConstant_nonneg (r + 2) r
  let C := (D + 1) * (A ^ derivativeMainExponent r + A ^ (-derivativeErrorExponent r) + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R Z L U hR hZ hL hU
  have hR0 : 0 < R := by linarith
  let mu := |Z| / R ^ (r + 3)
  have hmu : 0 < mu := by
    have hz := abs_pos.mpr hZ
    dsimp [mu]
    positivity
  have hid : ((r + 2).factorial : ℝ) * |Z| / (3 * R) ^ (r + 3) = A * mu := by
    dsimp [A, mu]
    rw [mul_pow]
    ring
  have h := reciprocal_sum_higher_derivative r R Z L U hR hZ hL hU
  dsimp only at h
  rw [hid, Real.mul_rpow hA.le hmu.le, Real.mul_rpow hA.le hmu.le] at h
  have ha0 : 0 ≤ A ^ derivativeMainExponent r := Real.rpow_nonneg hA.le _
  have hc0 : 0 ≤ A ^ (-derivativeErrorExponent r) := Real.rpow_nonneg hA.le _
  have hcoef1 : D * A ^ derivativeMainExponent r ≤ C := by dsimp [C]; nlinarith
  have hcoef2 : D * A ^ (-derivativeErrorExponent r) ≤ C := by dsimp [C]; nlinarith
  have hb1 := mul_le_mul_of_nonneg_right hcoef1
    (show 0 ≤ R * mu ^ derivativeMainExponent r by positivity)
  have hb2 := mul_le_mul_of_nonneg_right hcoef2
    (show 0 ≤ R ^ (1 - 2 * derivativeErrorExponent r) * mu ^ (-derivativeErrorExponent r) by positivity)
  change _ ≤ C * (R * mu ^ derivativeMainExponent r +
    R ^ (1 - 2 * derivativeErrorExponent r) * mu ^ (-derivativeErrorExponent r))
  change _ ≤ D * _ at h
  nlinarith only [h, hb1, hb2]

end BakerHarman
