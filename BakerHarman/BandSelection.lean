import BakerHarman.PowerBands

/-!
# Choosing derivative bands for Baker–Harman

We select the derivative order nearest to `K + 1`. The resulting finite chain
of bands will give saving `(6/5) * gammaBH K`, strictly above the required range
exponent. The estimates here retain the integer order explicitly.
-/

namespace BakerHarman

private lemma two_rpow_half_lower : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

private lemma band_endpoint_small_d (A d : ℝ) (hA : 4 ≤ A)
    (hdlo : 1 / 2 ≤ d) (hdhi : d ≤ 1) :
    (6 / 5 : ℝ) * (A - 2) ≤ d * (A * (2 : ℝ) ^ (2 - d) - 4) := by
  have hchord : (2 : ℝ) ^ d ≤ 1 + d := by
    have h := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (by norm_num)
      (show 0 ≤ d by linarith) hdhi
    norm_num at h ⊢
    exact h
  have hprod : (2 : ℝ) ^ d * 2 ^ (2 - d) = 4 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hfour : 4 ≤ (1 + d) * (2 : ℝ) ^ (2 - d) := by
    calc
      (4 : ℝ) = 2 ^ d * 2 ^ (2 - d) := hprod.symm
      _ ≤ (1 + d) * 2 ^ (2 - d) :=
        mul_le_mul_of_nonneg_right hchord (Real.rpow_nonneg (by norm_num) _)
  have hAd := mul_nonneg (sub_nonneg.mpr hA) (show 0 ≤ 14 * d - 6 by linarith)
  have hd2 : d ^ 2 ≤ d := by nlinarith
  have hpoly : (6 / 5 : ℝ) * (A - 2) * (1 + d) ≤ 4 * A * d - 4 * d * (1 + d) := by
    nlinarith only [hAd, hd2, hdlo]
  have hmul := mul_le_mul_of_nonneg_left hfour (show 0 ≤ A * d by positivity)
  apply (mul_le_mul_iff_right₀ (show 0 < 1 + d by linarith)).mp
  nlinarith only [hpoly, hmul]

private lemma band_overlap_large_A (A d : ℝ) (hA : 8 ≤ A) (hd : d ≤ 3 / 2) :
    (6 / 5 : ℝ) * (A - 2) ≤ A * (2 : ℝ) ^ (2 - d) - 4 := by
  have hp : (7 / 5 : ℝ) ≤ (2 : ℝ) ^ (2 - d) :=
    two_rpow_half_lower.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
  nlinarith [mul_le_mul_of_nonneg_left hp (show 0 ≤ A by linarith)]

private lemma band_endpoint_large_d (A d : ℝ) (hA : 8 ≤ A)
    (hdlo : 1 ≤ d) (hdhi : d ≤ 3 / 2) :
    (6 / 5 : ℝ) * (A - 2) ≤ d * (A * (2 : ℝ) ^ (2 - d) - 4) := by
  have hchord : (2 : ℝ) ^ (d - 1) ≤ d := by
    have h := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (by norm_num)
      (show 0 ≤ d - 1 by linarith) (show d - 1 ≤ 1 by linarith)
    norm_num at h
    linarith
  have hprod : (2 : ℝ) ^ (d - 1) * 2 ^ (2 - d) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have htwo : 2 ≤ d * (2 : ℝ) ^ (2 - d) := by
    calc
      (2 : ℝ) = 2 ^ (d - 1) * 2 ^ (2 - d) := hprod.symm
      _ ≤ d * 2 ^ (2 - d) :=
        mul_le_mul_of_nonneg_right hchord (Real.rpow_nonneg (by norm_num) _)
  nlinarith [mul_le_mul_of_nonneg_left htwo (show 0 ≤ A by linarith)]

/-- Saving used for the analytic estimate; the extra fifth leaves room for
constants in the lattice large-sum argument. -/
noncomputable def analyticSaving (K : ℝ) : ℝ := (6 / 5 : ℝ) * gammaBH K

lemma analyticSaving_bounds (K : ℝ) :
    gammaBH K < analyticSaving K ∧ analyticSaving K ≤ 3 / 10 := by
  unfold analyticSaving
  constructor
  · linarith [gammaBH_pos K]
  · linarith [gammaBH_le K]

/-- Derivative order nearest to `K + 1`. -/
noncomputable def selectedDerivativeOrder (K : ℝ) : ℕ := ⌊K + 3 / 2⌋₊

lemma selectedDerivativeOrder_bounds (K : ℝ) (hK : 1 ≤ K) :
    2 ≤ selectedDerivativeOrder K ∧
      1 / 2 < (selectedDerivativeOrder K : ℝ) - K ∧
      (selectedDerivativeOrder K : ℝ) - K ≤ 3 / 2 := by
  have hlo := Nat.floor_le (show 0 ≤ K + 3 / 2 by linarith)
  have hhi := Nat.lt_floor_add_one (K + 3 / 2)
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.le_floor_iff' (by decide : (2 : ℕ) ≠ 0)).mpr (by norm_num; linarith)
  · dsimp [selectedDerivativeOrder]
    linarith
  · dsimp [selectedDerivativeOrder]
    linarith

/-- The selected order has enough margin both for the preceding band overlap
and for the upper endpoint `K + 1`. -/
theorem selectedDerivativeOrder_margin (K : ℝ) (hK : 1 ≤ K) :
    analyticSaving K * ((2 : ℝ) ^ selectedDerivativeOrder K - 2) ≤ 1 ∧
      analyticSaving K * ((2 : ℝ) ^ selectedDerivativeOrder K - 2) ≤
        (selectedDerivativeOrder K : ℝ) - K := by
  obtain ⟨hj, hdlo, hdhi⟩ := selectedDerivativeOrder_bounds K hK
  let d := (selectedDerivativeOrder K : ℝ) - K
  let A := (2 : ℝ) ^ selectedDerivativeOrder K
  let G := (2 : ℝ) ^ (2 + K) - 4
  have hA : 4 ≤ A := by
    calc
      (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ A := pow_le_pow_right₀ (by norm_num) hj
  have hG4 : 4 ≤ G := by simpa [G, max_eq_right hK] using gammaBH_denom_ge K
  have hG : 0 < G := by linarith
  have hscale : G = A * (2 : ℝ) ^ (2 - d) - 4 := by
    dsimp [G, A, d]
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 2
    ring
  have hb : (6 / 5 : ℝ) * (A - 2) ≤ G ∧
      (6 / 5 : ℝ) * (A - 2) ≤ d * G := by
    by_cases hj2 : selectedDerivativeOrder K = 2
    · have hAeq : A = 4 := by norm_num [A, hj2]
      have hd1 : d ≤ 1 := by dsimp [d]; rw [hj2]; norm_num; linarith
      constructor
      · rw [hAeq]
        linarith
      · rw [hscale]
        exact band_endpoint_small_d A d hA hdlo.le hd1
    · have hj3 : 3 ≤ selectedDerivativeOrder K := by omega
      have hA8 : 8 ≤ A := by
        calc
          (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
          _ ≤ A := pow_le_pow_right₀ (by norm_num) hj3
      rw [hscale]
      refine ⟨band_overlap_large_A A d hA8 hdhi, ?_⟩
      by_cases hd1 : d ≤ 1
      · exact band_endpoint_small_d A d hA hdlo.le hd1
      · exact band_endpoint_large_d A d hA8 (not_le.mp hd1).le hdhi
  have hsaving : analyticSaving K = (6 / 5 : ℝ) / G := by
    unfold analyticSaving gammaBH
    rw [max_eq_right hK]
    dsimp [G]
    ring
  change analyticSaving K * (A - 2) ≤ 1 ∧ analyticSaving K * (A - 2) ≤ d
  rw [hsaving, div_mul_eq_mul_div]
  constructor
  · exact (div_le_iff₀ hG).mpr (by simpa using hb.1)
  · exact (div_le_iff₀ hG).mpr hb.2

/-- A finite chain of derivative bands covers the full interval of numerator
exponents from `2` to `K + 1`, with saving strictly above `gammaBH K`. -/
theorem exists_bakerHarman_band_cover (K : ℝ) (hK : 1 ≤ K) :
    ∃ m : ℕ, derivativeBandLower 0 (analyticSaving K) ≤ 2 ∧
      K + 1 ≤ derivativeBandUpper m (analyticSaving K) ∧
      ∀ r < m, ((2 : ℝ) ^ (r + 3) - 2) * analyticSaving K ≤ 1 := by
  obtain ⟨hj, _, _⟩ := selectedDerivativeOrder_bounds K hK
  obtain ⟨hoverlap, hend⟩ := selectedDerivativeOrder_margin K hK
  let m := selectedDerivativeOrder K - 2
  have hm : m + 2 = selectedDerivativeOrder K := by dsimp [m]; omega
  have hmr : (m : ℝ) + 2 = selectedDerivativeOrder K := by exact_mod_cast hm
  refine ⟨m, ?_, ?_, ?_⟩
  · norm_num [derivativeBandLower]
    linarith [(analyticSaving_bounds K).2]
  · unfold derivativeBandUpper
    rw [hm]
    push_cast
    linarith
  · intro r hr
    have hle : r + 3 ≤ selectedDerivativeOrder K := by omega
    have hp : (2 : ℝ) ^ (r + 3) ≤ 2 ^ selectedDerivativeOrder K :=
      pow_le_pow_right₀ (by norm_num) hle
    have hs : 0 ≤ analyticSaving K := (gammaBH_pos K).le.trans (analyticSaving_bounds K).1.le
    have h := mul_le_mul_of_nonneg_right (sub_le_sub_right hp 2) hs
    nlinarith

end BakerHarman
