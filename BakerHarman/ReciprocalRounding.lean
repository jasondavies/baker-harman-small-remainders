import BakerHarman.SimultaneousDirichlet

/-!
# Rounding a simultaneous approximant to a reciprocal modulus

If `r = floor (x / l)`, the rounding error in any nonnegative coordinate `a`
is at most `a / R²` whenever `r ≥ R > 0`.
-/

namespace BakerHarman

theorem reciprocal_rounding_error (a x l r R : ℝ) (ha : 0 ≤ a) (hx : 0 < x)
    (hR : 0 < R) (hRr : R ≤ r) (hlow : l * r ≤ x) (hupp : x ≤ l * (r + 1)) :
    |a / r - l * a / x| ≤ a / R ^ 2 := by
  have hr : 0 < r := hR.trans_le hRr
  have hgap0 : 0 ≤ x - l * r := by linarith
  have hgap : x - l * r ≤ x / r := by
    have hl : l ≤ x / r := (le_div_iff₀ hr).mpr hlow
    nlinarith only [hupp, hl]
  have he : a / r - l * a / x = (a / x) * (x - l * r) / r := by field_simp
  rw [he, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (a / x) * (x / r) / r := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (div_nonneg ha hx.le)) hr.le
    _ = a / r ^ 2 := by field_simp
    _ ≤ a / R ^ 2 := div_le_div_of_nonneg_left ha (sq_pos_of_pos hR)
      (pow_le_pow_left₀ hR.le hRr 2)

/-- A lower bound on `x / l` ensures its natural floor is an admissible
modulus, and the floor is at most `x` when `l ≥ 1`. -/
theorem reciprocal_floor_bounds (x l R : ℝ) (hx : 0 < x) (hl : 1 ≤ l)
    (_hR : 0 < R) (hlarge : R + 1 ≤ x / l) :
    R ≤ (⌊x / l⌋₊ : ℝ) ∧ (⌊x / l⌋₊ : ℝ) ≤ x ∧
      l * (⌊x / l⌋₊ : ℝ) ≤ x ∧ x ≤ l * ((⌊x / l⌋₊ : ℝ) + 1) := by
  have hl0 : 0 < l := by linarith
  have hlow := Nat.floor_le (div_nonneg hx.le hl0.le)
  have hupp := Nat.lt_floor_add_one (x / l)
  refine ⟨by linarith, hlow.trans (div_le_self hx.le hl), ?_, ?_⟩
  · nlinarith only [(le_div_iff₀ hl0).mp hlow]
  · nlinarith only [(div_lt_iff₀ hl0).mp hupp]

end BakerHarman
