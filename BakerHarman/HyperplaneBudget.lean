import BakerHarman.Defs

/-!
# Numerical budgets for hyperplane projection

These estimates control vector growth, logarithmic products, and projection
error in the sharp dimension induction. Power-range slack is handled by
`SharpDimensionInduction` itself.
-/

namespace BakerHarman

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
