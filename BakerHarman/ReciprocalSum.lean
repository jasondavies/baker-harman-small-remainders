import BakerHarman.Exponent
import BakerHarmanAnalytics.SecondDerivativeTest

/-!
# Reciprocal exponential sums for Baker–Harman

The phase is `exp(2π i x)`. We use the first- and second-derivative estimates
from the pinned `openai/math` source subset in `vendor/baker-harman-analytics`.
This file develops the analytic estimates needed by Baker–Harman's Lemma 1.
-/

open scoped BigOperators
open OAI.Problem337.ExponentialSum

namespace BakerHarman

private lemma reciprocal_increment {z : ℝ} {i : ℕ} (hi : 0 < i) :
    -z / ((i + 1 : ℕ) : ℝ) - -z / (i : ℝ) = z / ((i : ℝ) * (i + 1)) := by
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  have hi1 : (i : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The small-phase range in Baker–Harman's Lemma 1. The bound is uniform in
all natural subintervals of `[R,2R]`, and includes both endpoints. -/
theorem reciprocal_sum_small_phase (R z : ℝ) (a b : ℕ)
    (hR : 1 ≤ R) (hz : 0 < z) (hsmall : z ≤ R ^ 2 / 2)
    (ha : R ≤ a) (hb : (b : ℝ) ≤ 2 * R) :
    ‖∑ i ∈ Finset.Icc a b, phase (z / i)‖ ≤ 12 * R ^ 2 / z := by
  have hR0 : 0 < R := by linarith
  let β := z / (6 * R ^ 2)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβhalf : β ≤ 1 / 2 := by
    dsimp [β]
    apply (div_le_iff₀ (by positivity : 0 < 6 * R ^ 2)).2
    nlinarith
  have hipos (i : ℕ) (hi : a ≤ i) : 0 < i := by
    have hiR : R ≤ (i : ℝ) := ha.trans (by exact_mod_cast hi)
    exact_mod_cast (hR0.trans_le hiR)
  have hdenlo (i : ℕ) (hi : a ≤ i) : R ^ 2 ≤ (i : ℝ) * (i + 1) := by
    have hiR : R ≤ (i : ℝ) := ha.trans (by exact_mod_cast hi)
    nlinarith
  have hdenhi (i : ℕ) (hi : i ≤ b) : (i : ℝ) * (i + 1) ≤ 6 * R ^ 2 := by
    have hiR : (i : ℝ) ≤ 2 * R := (by exact_mod_cast hi : (i : ℝ) ≤ b).trans hb
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    nlinarith
  have h := first_derivative_sum_bound_Icc (fun i => -z / i) a b β 0 hβ
    (by
      intro i hi hj
      rw [reciprocal_increment (hipos i hi)]
      simp only [Int.cast_zero, zero_add]
      dsimp [β]
      apply (div_le_div_iff₀ (by positivity : 0 < 6 * R ^ 2)
        (by have := hipos i hi; positivity : 0 < (i : ℝ) * (i + 1))).2
      exact mul_le_mul_of_nonneg_left (hdenhi i hj) hz.le)
    (by
      intro i hi hj
      rw [reciprocal_increment (hipos i hi)]
      simp only [Int.cast_zero, zero_add]
      have hh : z / ((i : ℝ) * (i + 1)) ≤ 1 / 2 := by
        apply (div_le_iff₀ (by have := hipos i hi; positivity : 0 < (i : ℝ) * (i + 1))).2
        linarith [hdenlo i hi]
      linarith)
    (Or.inr (by
      intro i hi j hj hij
      dsimp only
      rw [reciprocal_increment (hipos i hi.1), reciprocal_increment (hipos j hj.1)]
      have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
      apply (div_le_div_iff₀
        (by have := hipos j hj.1; positivity : 0 < (j : ℝ) * (j + 1))
        (by have := hipos i hi.1; positivity : 0 < (i : ℝ) * (i + 1))).2
      apply mul_le_mul_of_nonneg_left _ hz.le
      exact mul_le_mul hijR (by linarith) (by positivity) (by positivity)))
  have hnorm : ‖∑ i ∈ Finset.Icc a b, phase (-z / i)‖ =
      ‖∑ i ∈ Finset.Icc a b, phase (z / i)‖ := by
    simp only [neg_div, phase_neg, ← map_sum, Complex.norm_conj]
  rw [hnorm] at h
  convert h using 1
  dsimp [β]
  field_simp
  ring

/-- The second-derivative estimate for reciprocal phases on a dyadic interval.
The explicit square-root terms retain the numerator dependence needed for
higher-order differencing. -/
theorem reciprocal_sum_second_derivative (R z : ℝ) (a b : ℕ)
    (hR : 0 < R) (hz : 0 < z) (hab : a ≤ b)
    (ha : R ≤ a) (hb : (b : ℝ) ≤ 2 * R) :
    ‖∑ i ∈ Finset.Ico a b, phase (z / i)‖ ≤
      63 * (((b - a : ℕ) : ℝ) * Real.sqrt (z / (4 * R ^ 3)) +
        1 / Real.sqrt (z / (4 * R ^ 3))) := by
  have hf (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
      HasDerivAt (fun y : ℝ => z / y) (-z / x ^ 2) x := by
    have hx0 : x ≠ 0 := ne_of_gt (hR.trans_le (ha.trans hx.1))
    simpa using (hasDerivAt_const x z).fun_div (hasDerivAt_id x) hx0
  have hf' (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
      HasDerivAt (fun y : ℝ => -z / y ^ 2) (2 * z / x ^ 3) x := by
    have hx0 : x ≠ 0 := ne_of_gt (hR.trans_le (ha.trans hx.1))
    convert (hasDerivAt_const x (-z)).div (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx0) using 1
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have hbound (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) :
      z / (4 * R ^ 3) ≤ |2 * z / x ^ 3| ∧
        |2 * z / x ^ 3| ≤ 8 * (z / (4 * R ^ 3)) := by
    have hxlo : R ≤ x := ha.trans hx.1
    have hxhi : x ≤ 2 * R := hx.2.trans hb
    have hx0 : 0 < x := hR.trans_le hxlo
    rw [abs_of_pos (by positivity : 0 < 2 * z / x ^ 3)]
    have hcubelo := pow_le_pow_left₀ hR.le hxlo 3
    have hcubehi := pow_le_pow_left₀ hx0.le hxhi 3
    constructor
    · apply (div_le_div_iff₀ (by positivity : 0 < 4 * R ^ 3)
        (by positivity : 0 < x ^ 3)).2
      nlinarith [mul_le_mul_of_nonneg_left hcubehi hz.le]
    · have heq : 8 * (z / (4 * R ^ 3)) = 2 * z / R ^ 3 := by ring
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hcubelo
  have h := second_derivative_test_Ico (fun x => z / x) (fun x => -z / x ^ 2)
    (fun x => 2 * z / x ^ 3) a b (z / (4 * R ^ 3)) 8 hab
    (by positivity) (by norm_num) hf hf' hbound
  norm_num at h ⊢
  exact h

/-- The complete reciprocal estimate for the base derivative order, valid up to
`z = R²`. Higher orders only need to handle numerators beyond this range. -/
theorem reciprocal_sum_base_order (R z : ℝ) (a b : ℕ)
    (hR : 1 ≤ R) (hz : 0 < z) (hzupper : z ≤ R ^ 2) (hab : a ≤ b)
    (ha : R ≤ a) (hb : (b : ℝ) ≤ 2 * R) :
    ‖∑ i ∈ Finset.Ico a b, phase (z / i)‖ ≤
      252 * (Real.sqrt R + R ^ 2 / z) := by
  have hR0 : 0 < R := by linarith
  by_cases hsmall : z ≤ R ^ 2 / 2
  · have ha0 : 0 < a := by exact_mod_cast (hR0.trans_le ha)
    have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
    have hset : Finset.Ico a b = Finset.Icc a (b - 1) := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hset]
    have h := reciprocal_sum_small_phase R z a (b - 1) hR hz hsmall ha
      ((by exact_mod_cast (Nat.sub_le b 1) : ((b - 1 : ℕ) : ℝ) ≤ b).trans hb)
    rw [mul_div_assoc] at h
    nlinarith [Real.sqrt_nonneg R, div_nonneg (sq_nonneg R) hz.le]
  have hzlower : R ^ 2 / 2 ≤ z := (not_le.mp hsmall).le
  let lam := z / (4 * R ^ 3)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hprod : (4 * R ^ 3) * lam = z := by
    dsimp [lam]
    field_simp
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR0
  have hlow : 1 ≤ 8 * R * lam := by
    have h := mul_le_mul_of_nonneg_left hzlower (show (0 : ℝ) ≤ 2 by norm_num)
    rw [← hprod] at h
    have hh : R ^ 2 * 1 ≤ R ^ 2 * (8 * R * lam) := by nlinarith only [h]
    exact (mul_le_mul_iff_right₀ hR2).mp hh
  have hhigh : 4 * R * lam ≤ 1 := by
    rw [← hprod] at hzupper
    have hh : R ^ 2 * (4 * R * lam) ≤ R ^ 2 * 1 := by nlinarith only [hzupper]
    exact (mul_le_mul_iff_right₀ hR2).mp hh
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
  have hfirst : 2 * R * Real.sqrt lam ≤ Real.sqrt R := by
    have h := mul_le_mul_of_nonneg_left hhigh hR0.le
    nlinarith [Real.sq_sqrt hlam.le, Real.sq_sqrt hR0.le]
  have hsecond : 1 / Real.sqrt lam ≤ 3 * Real.sqrt R := by
    apply (div_le_iff₀ hs).2
    have hp : 0 < Real.sqrt R * Real.sqrt lam := mul_pos hsR hs
    have heq : (Real.sqrt R * Real.sqrt lam) ^ 2 = R * lam := by
      rw [mul_pow, Real.sq_sqrt hR0.le, Real.sq_sqrt hlam.le]
    nlinarith
  have hlen : ((b - a : ℕ) : ℝ) ≤ 2 * R :=
    (by exact_mod_cast (Nat.sub_le b a) : ((b - a : ℕ) : ℝ) ≤ b).trans hb
  have hlenmul := mul_le_mul_of_nonneg_right hlen hs.le
  have h := reciprocal_sum_second_derivative R z a b hR0 hz hab ha hb
  change _ ≤ 63 * (((b - a : ℕ) : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) at h
  nlinarith [div_nonneg (sq_nonneg R) hz.le]

/-- Signed-numerator version of the base-order estimate. -/
theorem reciprocal_sum_base_order_abs (R z : ℝ) (a b : ℕ)
    (hR : 1 ≤ R) (hz : z ≠ 0) (hzupper : |z| ≤ R ^ 2) (hab : a ≤ b)
    (ha : R ≤ a) (hb : (b : ℝ) ≤ 2 * R) :
    ‖∑ i ∈ Finset.Ico a b, phase (z / i)‖ ≤
      252 * (Real.sqrt R + R ^ 2 / |z|) := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have h := reciprocal_sum_base_order R (-z) a b hR (by linarith)
      (by rwa [abs_of_neg hzneg] at hzupper) hab ha hb
    simp only [neg_div, phase_neg, ← map_sum, Complex.norm_conj] at h
    simpa only [abs_of_neg hzneg] using h
  · rw [abs_of_pos hzpos] at hzupper ⊢
    exact reciprocal_sum_base_order R z a b hR hzpos hzupper hab ha hb

/-- The base estimate on closed integer subintervals of `[R,2R]`. The extra
endpoint contributes one unit and is absorbed into the explicit constant. -/
theorem reciprocal_sum_base_order_int (R Z : ℝ) (L U : ℤ)
    (hR : 1 ≤ R) (hZ : Z ≠ 0) (hZupper : |Z| ≤ R ^ 2)
    (hL : R ≤ L) (hU : (U : ℝ) ≤ 2 * R) :
    ‖∑ n ∈ Finset.Icc L U, phase (Z / n)‖ ≤
      253 * (Real.sqrt R + R ^ 2 / |Z|) := by
  by_cases hempty : U < L
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity
  have hLU : L ≤ U := by omega
  have hL0 : 0 ≤ L := by exact_mod_cast (show (0 : ℝ) ≤ L by linarith)
  have hU0 : 0 ≤ U := hL0.trans hLU
  have hLa : (L.toNat : ℝ) = L := by exact_mod_cast Int.toNat_of_nonneg hL0
  have hUb : (U.toNat : ℝ) = U := by exact_mod_cast Int.toNat_of_nonneg hU0
  have hab : L.toNat ≤ U.toNat := Int.toNat_le_toNat hLU
  have h := reciprocal_sum_base_order_abs R Z L.toNat U.toNat hR hZ hZupper hab
    (by rwa [hLa]) (by rwa [hUb])
  have heq : (∑ n ∈ Finset.Icc L U, phase (Z / n)) =
      ∑ n ∈ Finset.Icc L.toNat U.toNat, phase (Z / n) := by
    apply Finset.sum_bij (fun n _ => n.toNat)
    · intro n hn
      obtain ⟨hnL, hnU⟩ := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨Int.toNat_le_toNat hnL, Int.toNat_le_toNat hnU⟩
    · intro n hn m hm hnm
      have hn0 := hL0.trans (Finset.mem_Icc.mp hn).1
      have hm0 := hL0.trans (Finset.mem_Icc.mp hm).1
      omega
    · intro n hn
      obtain ⟨hnL, hnU⟩ := Finset.mem_Icc.mp hn
      refine ⟨(n : ℤ), Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by simp⟩
    · intro n hn
      have hn0 := hL0.trans (Finset.mem_Icc.mp hn).1
      have hnreal : (n.toNat : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn0
      rw [hnreal]
  rw [heq]
  have hsum : (∑ n ∈ Finset.Icc L.toNat U.toNat, phase (Z / n)) =
      (∑ n ∈ Finset.Ico L.toNat U.toNat, phase (Z / n)) + phase (Z / U.toNat) := by
    exact (Finset.sum_Ico_add_eq_sum_Icc hab).symm
  rw [hsum]
  have ht := norm_add_le (∑ n ∈ Finset.Ico L.toNat U.toNat, phase (Z / n)) (phase (Z / U.toNat))
  rw [phase_norm] at ht
  have hs : 1 ≤ Real.sqrt R := by
    simpa using Real.sqrt_le_sqrt hR
  nlinarith [div_nonneg (sq_nonneg R) (abs_nonneg Z)]

end BakerHarman
