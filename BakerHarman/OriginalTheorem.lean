import BakerHarman.UnequalWeights

/-!
# Baker–Harman's full unequal-weight Theorem 1

The statement uses the logarithmic restriction printed in the paper, all real
vectors, every positive dimension, and the original rounded exponent (2.1).
A stronger version with the shifted-sets exponent is also given.
-/

namespace BakerHarman

/-- The explicit power exponent in Baker–Harman (1996), equation (2.1).
`bakerHarmanOrder K` is the least integer at least `1 + max K 1`. -/
noncomputable def originalExponent (K : ℝ) : ℝ :=
  1 / ((2 : ℝ) ^ (bakerHarmanOrder K + 1) - 4)

lemma originalExponent_denom_ge (K : ℝ) :
    (2 : ℝ) ^ (2 + max 1 K) - 4 ≤ (2 : ℝ) ^ (bakerHarmanOrder K + 1) - 4 := by
  have hh : 2 + max 1 K ≤ ((bakerHarmanOrder K + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [(bakerHarmanOrder_bounds K).1]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hh
  rw [Real.rpow_natCast] at h
  linarith

lemma originalExponent_pos (K : ℝ) : 0 < originalExponent K := by
  unfold originalExponent
  apply one_div_pos.mpr
  linarith [gammaBH_denom_ge K, originalExponent_denom_ge K]

lemma originalExponent_le_gammaBH (K : ℝ) : originalExponent K ≤ gammaBH K := by
  unfold originalExponent gammaBH
  exact one_div_le_one_div_of_le (by linarith [gammaBH_denom_ge K])
    (originalExponent_denom_ge K)

lemma logarithmic_tolerance_conversion (n : ℕ) (c Q : ℝ) (hc : 0 < c)
    (hlog : 1 ≤ Real.log Q) :
    ((2 : ℝ) ^ n / c)⁻¹ * (Real.log Q)⁻¹ ^ n ≤ c / (Real.log Q + 1) ^ n := by
  have hlog0 : 0 < Real.log Q := by linarith
  have hden : 0 < (Real.log Q + 1) ^ n := pow_pos (by linarith) _
  have hp : (Real.log Q + 1) ^ n ≤ (2 * Real.log Q) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  calc
    _ = c / (2 * Real.log Q) ^ n := by
      rw [inv_div, mul_pow, inv_pow]
      ring
    _ ≤ _ := div_le_div_of_nonneg_left hc.le hden hp

/-- The full unequal-weight conclusion, with exactly the paper's logarithmic
condition and the stronger shifted-sets exponent. `Q` and `R` may be real. -/
theorem bakerHarman_unequal_weights_log (n : ℕ) (hn : 0 < n) (K : ℝ) :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 0 < C₂ ∧ ∀ Q R : ℝ, 1 ≤ R → C₁ ≤ Q →
      Q ≤ R ^ gammaBH K → ∀ a ψ : Fin n → ℝ,
      Real.sqrt (∑ i, (a i) ^ 2) ≤ R ^ K → (∀ i, 0 < ψ i) →
      (∀ i, ψ i ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n) → (∏ i, ψ i) = Q⁻¹ →
      ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨c, Q₀, R₀, hc, hQ₀, hR₀, h⟩ := bakerHarman_unequal_weights n hn K
  refine ⟨max Q₀ (max R₀ (Real.exp 1)), (2 : ℝ) ^ n / c,
    hQ₀.trans (le_max_left _ _), by positivity, ?_⟩
  intro Q R hR hQ hQR a ψ ha hψ hψupper hprod
  have hQ₀Q : Q₀ ≤ Q := (le_max_left _ _).trans hQ
  have hR₀Q : R₀ ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hexpQ : Real.exp 1 ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hQleR : Q ≤ R := hQR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR
      (show gammaBH K ≤ 1 by linarith [gammaBH_le K]))
  have hlog : 1 ≤ Real.log Q := by
    have hh := Real.log_le_log (Real.exp_pos 1) hexpQ
    simpa only [Real.log_exp] using hh
  apply h Q R hQ₀Q (hR₀Q.trans hQleR) hQR a ψ ha hψ
  · intro i
    exact (hψupper i).trans (logarithmic_tolerance_conversion n c Q hc hlog)
  · exact hprod

/-- **Baker–Harman, Theorem 1** (1996), with its explicit exponent (2.1).
The dimension and growth exponent are positive; `Q,R` are natural numbers;
the vector may have arbitrary real coordinates. Constants depend only on `n,K`.
No additional size threshold for `R` or analytic hypothesis is assumed. -/
theorem bakerHarman_theorem_one (n : ℕ) (hn : 0 < n) (K : ℝ) (_hK : 0 < K) :
    ∃ C₁ C₂ : ℝ, 1 ≤ C₁ ∧ 0 < C₂ ∧ ∀ Q R : ℕ, C₁ ≤ Q →
      (Q : ℝ) ≤ (R : ℝ) ^ originalExponent K → ∀ a ψ : Fin n → ℝ,
      Real.sqrt (∑ i, (a i) ^ 2) ≤ (R : ℝ) ^ K → (∀ i, 0 < ψ i) →
      (∀ i, ψ i ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n) → (∏ i, ψ i) = (Q : ℝ)⁻¹ →
      ∃ r : ℕ, R ≤ r ∧ r ≤ 2 * Q * R ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := bakerHarman_unequal_weights_log n hn K
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro Q R hQ hQR a ψ ha hψ hψupper hprod
  have hRpos : 0 < R := by
    by_contra hR
    have he : R = 0 := by omega
    rw [he, Nat.cast_zero, Real.zero_rpow (originalExponent_pos K).ne'] at hQR
    linarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hRpos
  have hQR' : (Q : ℝ) ≤ (R : ℝ) ^ gammaBH K := hQR.trans
    (Real.rpow_le_rpow_of_exponent_le hR1 (originalExponent_le_gammaBH K))
  obtain ⟨r, hr, hrupper, herr⟩ := h Q R hR1 hQ hQR' a ψ ha hψ hψupper hprod
  exact ⟨r, by exact_mod_cast hr, by exact_mod_cast hrupper, herr⟩

end BakerHarman
