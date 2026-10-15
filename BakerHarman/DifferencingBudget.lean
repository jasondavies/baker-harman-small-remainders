import BakerHarman.Differencing

/-!
# Optimized differencing budgets

The shift length is chosen from the derivative scale rather than fixed in
advance. This preserves the exponent dependence needed for Baker–Harman.
-/

open scoped BigOperators
open ComplexConjugate
open OAI.Problem337

namespace BakerHarman

/-- An integer shift length at the scale `lam^(-q)`, with the two bounds
needed to balance the diagonal term and the growing correlation term. -/
lemma exists_differencing_length (R lam a q : ℝ)
    (hR : 1 ≤ R) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlamlo : R ^ (-(2 : ℝ)) ≤ lam)
    (ha : 0 < a) (ha1 : a ≤ 1) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hbalance : (1 - q) * a = q) :
    ∃ H : ℕ, 1 ≤ H ∧ (H : ℝ) ≤ 2 * R ∧
      1 / (H : ℝ) ≤ lam ^ q ∧ ((H : ℝ) * lam) ^ a ≤ 2 * lam ^ q := by
  have hR0 : 0 < R := by linarith
  let X := lam ^ (-q)
  have hX : 1 ≤ X := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hlam hlam1 (by linarith)
  have hX0 : 0 < X := by linarith
  have hXR : X ≤ R := by
    calc
      X ≤ (R ^ (-(2 : ℝ))) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hR0 _) hlamlo (by linarith)
      _ = R ^ (2 * q) := by rw [← Real.rpow_mul hR0.le]; congr 1; ring
      _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
      _ = R := Real.rpow_one R
  let H := ⌈X⌉₊
  have hHX : X ≤ (H : ℝ) := Nat.le_ceil _
  have hHupper : (H : ℝ) ≤ 2 * X := by
    have hceil := Nat.ceil_lt_add_one hX0.le
    change (H : ℝ) < X + 1 at hceil
    linarith
  have hH : 1 ≤ H := by exact_mod_cast (show (1 : ℝ) ≤ H by linarith)
  refine ⟨H, hH, by linarith, ?_, ?_⟩
  · have h := one_div_le_one_div_of_le hX0 hHX
    simpa only [X, Real.rpow_neg hlam.le, one_div, inv_inv] using h
  · have hmul : (H : ℝ) * lam ≤ 2 * lam ^ (1 - q) := by
      have h := mul_le_mul_of_nonneg_right hHupper hlam.le
      have hid : X * lam = lam ^ (1 - q) := by
        dsimp [X]
        conv_lhs => rhs; rw [← Real.rpow_one lam]
        rw [← Real.rpow_add hlam]
        congr 1
        ring
      calc
        (H : ℝ) * lam ≤ 2 * X * lam := h
        _ = 2 * lam ^ (1 - q) := by rw [mul_assoc, hid]
    calc
      ((H : ℝ) * lam) ^ a ≤ (2 * lam ^ (1 - q)) ^ a :=
        Real.rpow_le_rpow (by positivity) hmul ha.le
      _ = (2 : ℝ) ^ a * lam ^ q := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hlam.le, hbalance]
      _ ≤ 2 * lam ^ q := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlam.le _)
        calc
          (2 : ℝ) ^ a ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
          _ = 2 := by norm_num

private lemma two_term_square_bound (S X Y C : ℝ)
    (hS : 0 ≤ S) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (h : S ^ 2 ≤ 8 * (C + 1) * X ^ 2 + 4 * C * Y ^ 2) :
    S ≤ 4 * (C + 1) * (X + Y) := by
  have hcoefX : 8 * (C + 1) ≤ (4 * (C + 1)) ^ 2 := by nlinarith
  have hcoefY : 4 * C ≤ (4 * (C + 1)) ^ 2 := by nlinarith
  have hx := mul_le_mul_of_nonneg_right hcoefX (sq_nonneg X)
  have hy := mul_le_mul_of_nonneg_right hcoefY (sq_nonneg Y)
  have hcross := mul_nonneg (mul_nonneg (show 0 ≤ 4 * (C + 1) by positivity) hX)
    (mul_nonneg (show 0 ≤ 4 * (C + 1) by positivity) hY)
  have hsquared : S ^ 2 ≤ (4 * (C + 1) * (X + Y)) ^ 2 := by nlinarith
  exact (sq_le_sq₀ hS (by positivity)).mp hsquared

/-- One optimized A-process step in the nontrivial derivative-scale range.
The correlation bound retains both a growing and a decreasing power of the
shift, so the returned exponents can be iterated explicitly. -/
theorem van_der_corput_power_step_moderate (v : ℤ → ℂ) (N : ℕ)
    (R lam a c q C : ℝ) (hR : 1 ≤ R) (hN : (N : ℝ) ≤ 2 * R)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlamlo : R ^ (-(2 : ℝ)) ≤ lam)
    (ha : 0 < a) (ha1 : a ≤ 1) (hc : 0 ≤ c)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hbalance : (1 - q) * a = q)
    (hC : 0 ≤ C)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → v n = 0)
    (hnorm : ∀ n : ℤ, ‖v n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 0 < h →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v (n + h) * conj (v n)‖ ≤
        C * (R * ((h : ℝ) * lam) ^ a + R ^ (1 - 2 * c) * ((h : ℝ) * lam) ^ (-c))) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v n‖ ≤
      4 * (C + 1) * (R * lam ^ (q / 2) + R ^ (1 - c) * lam ^ (-c / 2)) := by
  have hR0 : 0 < R := by linarith
  obtain ⟨H, hH, hHR, hHinv, hHpow⟩ := exists_differencing_length R lam a q
    hR hlam hlam1 hlamlo ha ha1 hq hqhalf hbalance
  have hH0 : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  let E := C * (2 * R * lam ^ q + R ^ (1 - 2 * c) * lam ^ (-c))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcorrE (h : ℤ) (hh : 0 < h) (hhH : h < H) :
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v (n + h) * conj (v n)‖ ≤ E := by
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (show (1 : ℤ) ≤ h by omega)
    have hhHR : (h : ℝ) ≤ H := by exact_mod_cast hhH.le
    have hlow : lam ≤ (h : ℝ) * lam := by nlinarith
    have hupp : (h : ℝ) * lam ≤ (H : ℝ) * lam := mul_le_mul_of_nonneg_right hhHR hlam.le
    have hfirst : ((h : ℝ) * lam) ^ a ≤ 2 * lam ^ q :=
      (Real.rpow_le_rpow (by positivity) hupp ha.le).trans hHpow
    have hsecond : ((h : ℝ) * lam) ^ (-c) ≤ lam ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos hlam hlow (by linarith)
    apply (hcorr h hh).trans
    dsimp [E]
    apply mul_le_mul_of_nonneg_left _ hC
    have h1 := mul_le_mul_of_nonneg_left hfirst hR0.le
    have h2 := mul_le_mul_of_nonneg_left hsecond (Real.rpow_nonneg hR0.le (1 - 2 * c))
    nlinarith
  have hsym : ∀ h : ℤ, -(H : ℤ) < h → h < H → h ≠ 0 →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v (n + h) * conj (v n)‖ ≤ E := by
    intro h hl hu hn
    by_cases hp : 0 < h
    · exact hcorrE h hp hu
    · have heq := interval_correlation_neg v N (-h) hsupport
      simp only [neg_neg] at heq
      rw [heq, Complex.norm_conj]
      exact hcorrE (-h) (by omega) (by omega)
  have hraw := van_der_corput_interval_exact v N H hH E hE hsupport hnorm hsym
  have hdiag : (N : ℝ) / H ≤ 2 * R * lam ^ q := by
    calc
      (N : ℝ) / H = (N : ℝ) * (1 / (H : ℝ)) := by ring
      _ ≤ (2 * R) * lam ^ q := mul_le_mul hN hHinv (by positivity) (by positivity)
  have hraw' : ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v n‖ ^ 2 ≤
      4 * R * (2 * R * lam ^ q + E) := by
    apply hraw.trans
    exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  let X := R * lam ^ (q / 2)
  let Y := R ^ (1 - c) * lam ^ (-c / 2)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hx : X ^ 2 = R ^ 2 * lam ^ q := by
    dsimp [X]
    rw [mul_pow, ← Real.rpow_mul_natCast hlam.le]
    congr 2
    norm_num
  have hy : Y ^ 2 = R * R ^ (1 - 2 * c) * lam ^ (-c) := by
    dsimp [Y]
    rw [mul_pow, ← Real.rpow_mul_natCast hR0.le, ← Real.rpow_mul_natCast hlam.le]
    have hr : R * R ^ (1 - 2 * c) = R ^ ((1 - c) * (2 : ℕ)) := by
      conv_lhs => lhs; rw [← Real.rpow_one R]
      rw [← Real.rpow_add hR0]
      congr 1
      norm_num
      ring
    rw [hr]
    congr 2
    norm_num
  apply two_term_square_bound _ X Y C (norm_nonneg _) hX hY hC
  rw [hx, hy]
  dsimp [E] at hraw'
  nlinarith only [hraw']

/-- The optimized A-process step for every positive derivative scale. Outside
the nontrivial range, one of the two output terms already dominates the trivial
length bound. -/
theorem van_der_corput_power_step (v : ℤ → ℂ) (N : ℕ)
    (R lam a c q C : ℝ) (hR : 1 ≤ R) (hN : (N : ℝ) ≤ 2 * R)
    (hlam : 0 < lam) (ha : 0 < a) (ha1 : a ≤ 1) (hc : 0 ≤ c)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hbalance : (1 - q) * a = q)
    (hC : 0 ≤ C)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → v n = 0)
    (hnorm : ∀ n : ℤ, ‖v n‖ ≤ 1)
    (hcorr : ∀ h : ℤ, 0 < h →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v (n + h) * conj (v n)‖ ≤
        C * (R * ((h : ℝ) * lam) ^ a + R ^ (1 - 2 * c) * ((h : ℝ) * lam) ^ (-c))) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v n‖ ≤
      4 * (C + 1) * (R * lam ^ (q / 2) + R ^ (1 - c) * lam ^ (-c / 2)) := by
  have hR0 : 0 < R := by linarith
  have htriv : ‖∑ n ∈ Finset.Icc (1 : ℤ) N, v n‖ ≤ 2 * R := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc (1 : ℤ) N, ‖v n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Icc (1 : ℤ) N, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hnorm n)
      _ = (N : ℝ) := by simp [Int.card_Icc]
      _ ≤ 2 * R := hN
  have hX : 0 ≤ R * lam ^ (q / 2) := by positivity
  have hY : 0 ≤ R ^ (1 - c) * lam ^ (-c / 2) := by positivity
  have hCterm := mul_nonneg hC (add_nonneg hX hY)
  by_cases hbig : 1 ≤ lam
  · have hp : 1 ≤ lam ^ (q / 2) := Real.one_le_rpow hbig (by positivity)
    have hXlo := mul_le_mul_of_nonneg_left hp hR0.le
    nlinarith
  by_cases hsmall : lam ≤ R ^ (-(2 : ℝ))
  · have hp : (R ^ (-(2 : ℝ))) ^ (-c / 2) ≤ lam ^ (-c / 2) :=
      Real.rpow_le_rpow_of_nonpos hlam hsmall (by linarith)
    have hYlo := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hR0.le (1 - c))
    have heq : R ^ (1 - c) * (R ^ (-(2 : ℝ))) ^ (-c / 2) = R := by
      rw [← Real.rpow_mul hR0.le, ← Real.rpow_add hR0]
      convert Real.rpow_one R using 1
      congr 1
      ring
    rw [heq] at hYlo
    nlinarith
  exact van_der_corput_power_step_moderate v N R lam a c q C hR hN hlam
    (not_le.mp hbig).le (not_le.mp hsmall).le ha ha1 hc hq hqhalf hbalance hC
    hsupport hnorm hcorr

/-- The optimized step on a translated integer interval. Positive correlations
are exactly the phase differences on intervals shortened by the shift. -/
theorem translated_interval_phase_power_step (f : ℝ → ℝ) (L : ℤ) (N : ℕ)
    (R lam a c q C : ℝ) (hR : 1 ≤ R) (hN : (N : ℝ) ≤ 2 * R)
    (hlam : 0 < lam) (ha : 0 < a) (ha1 : a ≤ 1) (hc : 0 ≤ c)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hbalance : (1 - q) * a = q)
    (hC : 0 ≤ C)
    (hcorr : ∀ h : ℤ, 0 < h →
      ‖∑ n ∈ Finset.Icc L (L + (N : ℤ) - 1 - h),
        differencingPhase (f ((n : ℝ) + h) - f n)‖ ≤
        C * (R * ((h : ℝ) * lam) ^ a + R ^ (1 - 2 * c) * ((h : ℝ) * lam) ^ (-c))) :
    ‖∑ n ∈ Finset.Icc L (L + (N : ℤ) - 1), differencingPhase (f n)‖ ≤
      4 * (C + 1) * (R * lam ^ (q / 2) + R ^ (1 - c) * lam ^ (-c / 2)) := by
  let g : ℝ → ℝ := fun x => f (x + ((L - 1 : ℤ) : ℝ))
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → intervalPhase g 1 N n = 0 := by
    intro n hn
    simpa only [intervalPhase, Finset.mem_Icc, ite_eq_right_iff] using
      (fun h : (1 : ℤ) ≤ n ∧ n ≤ N => False.elim (hn (Finset.mem_Icc.mpr h)))
  have hnrm : ∀ n : ℤ, ‖intervalPhase g 1 N n‖ ≤ 1 := by
    intro n
    unfold intervalPhase
    split_ifs <;> simp
  have hbound := van_der_corput_power_step (intervalPhase g 1 N) N R lam a c q C
    hR hN hlam ha ha1 hc hq hqhalf hbalance hC hsupp hnrm (by
      intro h hh
      change ‖∑ n ∈ Finset.Icc (1 : ℤ) N, correlationShift (intervalPhase g 1 N) h n‖ ≤ _
      rw [correlationShift_intervalPhase g 1 N h hh.le,
        intervalPhase_sum _ 1 ((N : ℤ) - h) 1 N le_rfl (by omega)]
      have hdiff (x : ℝ) : g (x + h) - g x =
          (fun y => f (y + h) - f y) (x + ((L - 1 : ℤ) : ℝ)) := by
        dsimp [g]
        congr 2
        ring
      simp_rw [hdiff]
      rw [phase_sum_integer_translate (fun y => f (y + h) - f y) 1 ((N : ℤ) - h) (L - 1)]
      have hleft : (1 : ℤ) + (L - 1) = L := by omega
      have hright : ((N : ℤ) - h) + (L - 1) = L + (N : ℤ) - 1 - h := by omega
      rw [hleft, hright]
      exact hcorr h hh)
  rw [intervalPhase_sum g 1 N 1 N le_rfl le_rfl] at hbound
  dsimp [g] at hbound
  rw [phase_sum_integer_translate] at hbound
  have hleft : (1 : ℤ) + (L - 1) = L := by omega
  have hright : (N : ℤ) + (L - 1) = L + (N : ℤ) - 1 := by omega
  rwa [hleft, hright] at hbound

end BakerHarman
