import BakerHarman.LogFactors

/-!
# Logarithmic budgets for dimension induction

The Gaussian frequency radius grows like `log Q + 1`. Increasing the logarithmic
power in the new reciprocal scale absorbs this radius while retaining exactly
the same power condition `Q ≤ R ^ γ` in the lower-dimensional problem.
-/

namespace BakerHarman

/-- A strictly larger logarithmic exponent absorbs every fixed coefficient. -/
theorem log_add_one_rpow_dominates (C a b : ℝ) (hab : b < a) :
    ∀ᶠ Q : ℝ in Filter.atTop,
      C * (Real.log Q + 1) ^ b ≤ (Real.log Q + 1) ^ a := by
  have hL : Filter.Tendsto (fun Q : ℝ => Real.log Q + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ Real.tendsto_log_atTop
  have h := ((tendsto_rpow_atTop (sub_pos.mpr hab)).comp hL).eventually_ge_atTop C
  filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with Q h hQ
  have hL0 : 0 < Real.log Q + 1 := by linarith [Real.log_nonneg hQ]
  calc
    _ ≤ (Real.log Q + 1) ^ (a - b) * (Real.log Q + 1) ^ b :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hL0.le _)
    _ = _ := by rw [← Real.rpow_add hL0]; congr 1; ring

/-- A logarithmic degree depending only on the fixed power exponent suffices
for every fixed scaling and detection constant. -/
theorem exists_hyperplane_log_budget (γ : ℝ) (hγ : 0 < γ) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ A C c : ℝ, 0 < A → 0 < C → 0 < c →
      ∀ᶠ Q : ℝ in Filter.atTop, 1 ≤ Q ∧
        max c 2 * C * (Real.log Q + 1) ≤ (Real.log Q + 1) ^ J ∧
        A * (C * (Real.log Q + 1)) ^ (γ + 1) ≤ ((Real.log Q + 1) ^ J) ^ γ ∧
        A * C * (Real.log Q + 1) ≤ Q := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (max 1 ((γ + 1) / γ))
  have hJ1 : (1 : ℝ) < J := lt_of_le_of_lt (le_max_left _ _) hJ
  have hJγ : γ + 1 < (J : ℝ) * γ :=
    (div_lt_iff₀ hγ).mp (lt_of_le_of_lt (le_max_right _ _) hJ)
  refine ⟨J, by exact_mod_cast hJ1.le, ?_⟩
  intro A C c _ hC _
  filter_upwards [log_add_one_rpow_dominates (max c 2 * C) J 1 hJ1,
    log_add_one_rpow_dominates (A * C ^ (γ + 1)) ((J : ℝ) * γ) (γ + 1) hJγ,
    log_add_one_pow_absorbed (A * C) 1 1 (by norm_num),
    Filter.eventually_ge_atTop (1 : ℝ)] with Q hscale hpower hlog hQ
  have hL0 : 0 ≤ Real.log Q + 1 := by linarith [Real.log_nonneg hQ]
  refine ⟨hQ, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_natCast, Real.rpow_one] using hscale
  · rw [Real.mul_rpow hC.le hL0, ← mul_assoc, ← Real.rpow_natCast (Real.log Q + 1) J,
      ← Real.rpow_mul hL0]
    exact hpower
  · simpa only [pow_one, Real.rpow_one] using hlog

/-- The numerical change of scales preserves the power range and gives uniform
control of the new logarithm. The covolume multiplier is denoted by `A`. -/
theorem hyperplane_rescaling_bounds (γ R Q p A C c : ℝ) (J : ℕ)
    (hγ : 0 < γ) (hR : 0 < R) (hQ : 1 ≤ Q) (hp : 0 < p)
    (hA : 0 < A) (hC : 0 < C) (hc : 0 < c)
    (hQR : Q ≤ R ^ γ) (hpC : p ≤ C * (Real.log Q + 1))
    (hscale : max c 2 * C * (Real.log Q + 1) ≤ (Real.log Q + 1) ^ J)
    (hpower : A * (C * (Real.log Q + 1)) ^ (γ + 1) ≤ ((Real.log Q + 1) ^ J) ^ γ)
    (hlog : A * C * (Real.log Q + 1) ≤ Q) :
    c * R ≤ R / p * (Real.log Q + 1) ^ J ∧
      2 * C * R * (Real.log Q + 1) / p ≤ R / p * (Real.log Q + 1) ^ J ∧
      A * p * Q ≤ (R / p * (Real.log Q + 1) ^ J) ^ γ ∧
      Real.log (A * p * Q) + 1 ≤ 2 * (Real.log Q + 1) := by
  let L := Real.log Q + 1
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hQ]
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hcp : c * p ≤ L ^ J := by
    calc
      _ ≤ c * (C * L) := mul_le_mul_of_nonneg_left hpC hc.le
      _ ≤ max c 2 * C * L := by
        nlinarith [mul_le_mul_of_nonneg_right (le_max_left c 2) (mul_nonneg hC.le hL.le)]
      _ ≤ _ := hscale
  have htwo : 2 * C * L ≤ L ^ J := by
    calc
      _ ≤ max c 2 * C * L := by
        nlinarith [mul_le_mul_of_nonneg_right (le_max_right c 2) (mul_nonneg hC.le hL.le)]
      _ ≤ _ := hscale
  have hpow : A * p ^ (γ + 1) ≤ (L ^ J) ^ γ :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le hpC (by linarith)) hA.le).trans hpower
  have hratio : A * p ≤ (L ^ J) ^ γ / p ^ γ := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hp γ)).mpr
    rw [Real.rpow_add hp, Real.rpow_one] at hpow
    nlinarith [hpow]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change c * R ≤ R / p * L ^ J
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]
    nlinarith [mul_le_mul_of_nonneg_left hcp hR.le]
  · change 2 * C * R * L / p ≤ R / p * L ^ J
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp]
    nlinarith [mul_le_mul_of_nonneg_left htwo hR.le]
  · change A * p * Q ≤ (R / p * L ^ J) ^ γ
    rw [Real.mul_rpow (div_nonneg hR.le hp.le) (pow_nonneg hL.le _),
      Real.div_rpow hR.le hp.le]
    calc
      _ ≤ A * p * R ^ γ := mul_le_mul_of_nonneg_left hQR (by positivity)
      _ ≤ R ^ γ * ((L ^ J) ^ γ / p ^ γ) := by
        nlinarith [mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hR.le γ)]
      _ = _ := by ring
  · have hQ' : A * p * Q ≤ Q ^ 2 := by
      have hpQ := mul_le_mul_of_nonneg_left hpC hA.le
      have hu : A * p ≤ Q := by nlinarith [hpQ, hlog]
      nlinarith [mul_le_mul_of_nonneg_right hu hQ0.le]
    have hh := Real.log_le_log (by positivity : 0 < A * p * Q) hQ'
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith

/-- Enlarging the reciprocal scale by at least `c` accommodates scaling the
vector by `c`, for every input growth exponent at least one. -/
theorem hyperplane_scaled_growth (c R S a : ℝ) (hc : 1 ≤ c) (hR : 0 ≤ R)
    (ha : 1 ≤ a) (hS : c * R ≤ S) : c * R ^ a ≤ S ^ a := by
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  calc
    _ ≤ c ^ a * R ^ a := mul_le_mul_of_nonneg_right
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hc ha)
      (Real.rpow_nonneg hR a)
    _ = (c * R) ^ a := (Real.mul_rpow hc0 hR).symm
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hc0 hR) hS (le_trans zero_le_one ha)

/-- Product estimate used for both the input norm and output modulus bounds
in the lower-dimensional problem. -/
theorem hyperplane_log_product_bound (R Q R' Q' A L L' : ℝ) (J n : ℕ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hL : 0 ≤ L) (hL' : 0 ≤ L')
    (hlog : L' ≤ 2 * L) (hprod : R' * Q' = A * R * Q * L ^ J) :
    R' * Q' * L' ^ n ≤ A * 2 ^ n * R * Q * L ^ (J + n) := by
  rw [hprod]
  calc
    _ ≤ A * R * Q * L ^ J * (2 * L) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL' hlog n) (by positivity)
    _ = _ := by rw [mul_pow, pow_add]; ring

/-- The dual lower bound turns a scalar-product bound into a bound for the
normal projection error. -/
theorem hyperplane_error_budget (Z p δ C R Q L : ℝ) (hp : 0 < p) (hδ : 0 < δ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hlower : δ ≤ p * Q) (hZ : Z ≤ C * R * L) :
    Z / p ≤ C / δ * R * Q * L := by
  apply (div_le_iff₀ hp).mpr
  have h := mul_le_mul_of_nonneg_left hlower (show 0 ≤ C * R * L / δ by positivity)
  have he : (C * R * L / δ) * δ = C * R * L := div_mul_cancel₀ _ hδ.ne'
  rw [he] at h
  calc
    _ ≤ C * R * L := hZ
    _ ≤ (C * R * L / δ) * (p * Q) := h
    _ = _ := by ring

/-- Lower input bounds survive projection once the normal error is budgeted.
The same logarithmic degree handles every vector and lattice at this stage. -/
theorem hyperplane_projected_lower_budget
    (R Q R' Q' A c E D a y z L L' : ℝ) (J n : ℕ)
    (hR : 0 ≤ R) (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hc : 1 ≤ c)
    (hE : 0 ≤ E) (ha : 0 ≤ a) (hz : 0 ≤ z) (hL : 1 ≤ L) (hL' : 0 ≤ L')
    (hn : 1 ≤ n) (hlog : L' ≤ 2 * L) (hprod : R' * Q' = A * R * Q * L ^ J)
    (hD : E + a * A * 2 ^ n ≤ D)
    (hy : D * R * Q * L ^ (J + n) ≤ y) (herror : y ≤ z + E * R * Q * L) :
    a * R' * Q' * L' ^ n ≤ c * z := by
  let S := R * Q * L ^ (J + n)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hpow : L ≤ L ^ (J + n) := le_self_pow₀ hL (by omega)
  have he : E * R * Q * L ≤ E * S := by
    dsimp [S]
    nlinarith [mul_le_mul_of_nonneg_left hpow (show 0 ≤ E * R * Q by positivity)]
  have hlower : (a * A * 2 ^ n) * S ≤ z := by
    have h := mul_le_mul_of_nonneg_right hD hS
    have hy' : D * S ≤ y := by dsimp [S]; nlinarith [hy]
    nlinarith [h, he, herror, hy']
  have hprod_bound := hyperplane_log_product_bound R Q R' Q' A L L' J n hR hQ hA
    (le_trans zero_le_one hL) hL' hlog hprod
  calc
    _ ≤ a * (A * 2 ^ n * R * Q * L ^ (J + n)) := by
      nlinarith [mul_le_mul_of_nonneg_left hprod_bound ha]
    _ = (a * A * 2 ^ n) * S := by dsimp [S]; ring
    _ ≤ z := hlower
    _ ≤ c * z := le_mul_of_one_le_left hz hc

end BakerHarman
