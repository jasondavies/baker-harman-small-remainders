import BakerHarman.LogFactors

/-!
# Budgets for equal coordinate tolerances

Equal weights `Q ^ (-1/n)` absorb every fixed logarithmic power. A rounded
Dirichlet box size leaves a fixed part of the error budget for rounding the
reciprocal modulus.
-/

namespace BakerHarman

noncomputable def equalWeight (n : ℕ) (Q : ℝ) : ℝ := Q ^ (-(n : ℝ)⁻¹)

theorem equalWeight_pos (n : ℕ) {Q : ℝ} (hQ : 0 < Q) : 0 < equalWeight n Q :=
  Real.rpow_pos_of_pos hQ _

theorem equalWeight_le_one (n : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) : equalWeight n Q ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hQ (neg_nonpos.mpr (inv_nonneg.mpr (Nat.cast_nonneg n)))

theorem equalWeight_inv (n : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) :
    (equalWeight n Q)⁻¹ = Q ^ (n : ℝ)⁻¹ := by
  rw [equalWeight, Real.rpow_neg hQ, inv_inv]

theorem equalWeight_pow (n : ℕ) (hn : 0 < n) {Q : ℝ} (hQ : 0 < Q) :
    equalWeight n Q ^ n = Q⁻¹ := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [equalWeight, ← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
  rw [neg_mul, inv_mul_cancel₀ hn0, Real.rpow_neg_one]

theorem equalWeight_remaining_product (n : ℕ) (hn : 0 < n) {Q : ℝ} (hQ : 0 < Q) :
    equalWeight n Q ^ (n - 1) * (Q * equalWeight n Q) = 1 := by
  have he : equalWeight n Q ^ (n - 1) * equalWeight n Q = Q⁻¹ := by
    rw [← pow_succ, Nat.sub_add_cancel hn, equalWeight_pow n hn hQ]
  calc
    _ = (equalWeight n Q ^ (n - 1) * equalWeight n Q) * Q := by ring
    _ = 1 := by rw [he, inv_mul_cancel₀ hQ.ne']

/-- Every fixed logarithmic power is smaller than the reciprocal coordinate
scale for sufficiently large `Q`. -/
theorem equalWeight_log_pow_small (n : ℕ) (hn : 0 < n) (C : ℝ) (m : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ Q : ℝ in Filter.atTop, C * equalWeight n Q * (Real.log Q + 1) ^ m ≤ δ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  filter_upwards [log_add_one_pow_absorbed (C / δ) (n : ℝ)⁻¹ m (inv_pos.mpr hnpos),
    Filter.eventually_ge_atTop (1 : ℝ)] with Q h hQ
  have hQ0 : 0 < Q := by linarith
  have hψ : 0 < equalWeight n Q := equalWeight_pos n hQ0
  calc
    _ = δ * ((C / δ) * (Real.log Q + 1) ^ m) * equalWeight n Q := by field_simp
    _ ≤ δ * Q ^ (n : ℝ)⁻¹ * equalWeight n Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hδ.le) hψ.le
    _ = δ := by
      rw [equalWeight, mul_assoc, ← Real.rpow_add hQ0, add_neg_cancel, Real.rpow_zero, mul_one]

/-- For equal weights there is a uniform positive error margin after choosing
the integer Dirichlet box size. -/
theorem equalWeight_dirichlet_budget (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ ∀ᶠ Q : ℝ in Filter.atTop,
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ^ (n - 1) ≤ (5 / 4 : ℝ) * Q * equalWeight n Q ∧
        1 / (M : ℝ) ≤ s * equalWeight n Q := by
  let d := n - 1
  have hd : 0 < d := by dsimp [d]; omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let α : ℝ := (9 / 8 : ℝ) ^ (d : ℝ)⁻¹
  let β : ℝ := (5 / 4 : ℝ) ^ (d : ℝ)⁻¹
  have hα : 1 < α := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hdR)
  have hα0 : 0 < α := by linarith
  have hαβ : α < β := Real.rpow_lt_rpow (by norm_num) (by norm_num) (inv_pos.mpr hdR)
  have hβpow : β ^ d = (5 / 4 : ℝ) := by
    dsimp only [β]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5 / 4),
      inv_mul_cancel₀ hdR.ne', Real.rpow_one]
  refine ⟨α⁻¹, inv_pos.mpr hα0, inv_lt_one_of_one_lt₀ hα, ?_⟩
  filter_upwards [equalWeight_log_pow_small n (by omega) 1 0 (β - α) (sub_pos.mpr hαβ),
    Filter.eventually_ge_atTop (1 : ℝ)] with Q hsmall hQ
  have hQ0 : 0 < Q := by linarith
  let ψ := equalWeight n Q
  have hψ : 0 < ψ := equalWeight_pos n hQ0
  have hψsmall : ψ ≤ β - α := by simpa only [pow_zero, mul_one, one_mul] using hsmall
  let M := ⌈α / ψ⌉₊
  have hM : 0 < M := Nat.ceil_pos.mpr (div_pos hα0 hψ)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hMlo : α / ψ ≤ M := Nat.le_ceil _
  have hMhi : (M : ℝ) < α / ψ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMψ : (M : ℝ) * ψ ≤ β := by
    have he : (α / ψ + 1) * ψ = α + ψ := by field_simp
    have hh := mul_lt_mul_of_pos_right hMhi hψ
    rw [he] at hh
    linarith
  refine ⟨M, hM, ?_, ?_⟩
  · have hpow := pow_le_pow_left₀ (mul_nonneg hM0.le hψ.le) hMψ d
    rw [mul_pow, hβpow] at hpow
    have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ Q * ψ by positivity)
    have he : ψ ^ d * (Q * ψ) = 1 := equalWeight_remaining_product n (by omega) hQ0
    have hr : ((M : ℝ) ^ d * ψ ^ d) * (Q * ψ) = (M : ℝ) ^ d := by
      rw [mul_assoc, he, mul_one]
    rw [hr] at hmul
    simpa only [d, mul_assoc] using hmul
  · have hαM : α ≤ (M : ℝ) * ψ := (div_le_iff₀ hψ).mp hMlo
    apply (div_le_iff₀ hM0).mpr
    have hh := mul_le_mul_of_nonneg_left hαM (inv_pos.mpr hα0).le
    rw [inv_mul_cancel₀ hα0.ne'] at hh
    nlinarith only [hh]

/-- The power range leaves room for the rounding error, uniformly in `Q`. -/
theorem log_product_power_range_small (K A : ℝ) (hA : 0 ≤ A) (m : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ Q : ℝ, 1 ≤ Q → Q ≤ R ^ gammaBH K →
      A * Q * (Real.log Q + 1) ^ m ≤ δ * R := by
  filter_upwards [log_add_one_pow_absorbed (A / δ) (1 / 2) m (by norm_num),
    Filter.eventually_ge_atTop (1 : ℝ)] with R hlog hR
  intro Q hQ hQR
  have hR0 : 0 < R := by linarith
  have hQ0 : 0 < Q := by linarith
  have hQR' : Q ≤ R := hQR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR
      (show gammaBH K ≤ 1 by linarith [gammaBH_le K]))
  have hlogs : (Real.log Q + 1) ^ m ≤ (Real.log R + 1) ^ m :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg hQ])
      (by linarith [Real.log_le_log hQ0 hQR']) m
  have hAR : A * (Real.log R + 1) ^ m ≤ δ * R ^ (1 / 2 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hlog hδ.le
    have he : δ * ((A / δ) * (Real.log R + 1) ^ m) = A * (Real.log R + 1) ^ m := by field_simp
    rwa [he] at hh
  calc
    _ ≤ Q * (A * (Real.log R + 1) ^ m) := by
      nlinarith only [mul_le_mul_of_nonneg_left hlogs (mul_nonneg hA hQ0.le)]
    _ ≤ Q * (δ * R ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hAR hQ0.le
    _ ≤ R ^ gammaBH K * (δ * R ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hQR (by positivity)
    _ = δ * R ^ (gammaBH K + 1 / 2) := by rw [Real.rpow_add hR0]; ring
    _ ≤ δ * R := mul_le_mul_of_nonneg_left (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR
        (show gammaBH K + 1 / 2 ≤ 1 by linarith [gammaBH_le K])) hδ.le

end BakerHarman
