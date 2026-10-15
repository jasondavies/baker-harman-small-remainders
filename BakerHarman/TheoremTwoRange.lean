import BakerHarman.TheoremTwo

/-!
# The substantive growth range of Theorem 2

`TheoremTwoAdmissible` records the natural-parameter theorem's hypotheses on
`Q,R,a,ψ`. For every positive dimension, every `K > 1`, every real `C₁`,
and every `C₂ > 0`, admissible inputs exist with arbitrarily large `R`. For
`K ≤ 1`, they do not exist when `exp 1 ≤ C₁` and `1 ≤ C₂`, the bounds exported
by `bakerHarman_theorem_two_constants`.
-/

namespace BakerHarman

/-- The hypotheses cannot hold for `K ≤ 1` when the constants satisfy the
bounds exported by `bakerHarman_theorem_two_constants`. -/
theorem theoremTwo_not_admissible (n : ℕ) (hn : 0 < n) (K C₁ C₂ : ℝ)
    (hK : K ≤ 1) (hC₁ : Real.exp 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (Q R : ℕ) (a ψ : Fin n → ℝ) : ¬ TheoremTwoAdmissible n hn K C₁ C₂ Q R a ψ := by
  rintro ⟨hQ, hQR, ha, hψ, hψupper, hprod, hlarge⟩
  have hQ2 : (2 : ℝ) < Q := Real.exp_one_gt_two.trans_le (hC₁.trans hQ)
  have hQ3 : (3 : ℝ) ≤ Q := by exact_mod_cast (show 3 ≤ Q by exact_mod_cast hQ2)
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlog : 1 < Real.log Q := by
    have h := Real.log_lt_log (Real.exp_pos 1) (Real.exp_one_lt_three.trans_le hQ3)
    simpa only [Real.log_exp] using h
  have hlog0 : 0 < Real.log Q := by linarith
  obtain ⟨hR1, _⟩ := originalExponent_nat_parameters K Q R (by linarith) hQR
  have hR0 : (0 : ℝ) < R := by linarith
  have hψ1 (i) : ψ i ≤ 1 := by
    apply (hψupper i).trans
    have hi := inv_le_one_of_one_le₀ hC₂
    have hp := pow_le_one₀ (inv_nonneg.mpr hlog0.le) (inv_le_one_of_one_le₀ hlog.le) (n := n)
    simpa using mul_le_mul hi hp (by positivity) (show (0 : ℝ) ≤ 1 by norm_num)
  have haR : Real.sqrt (∑ i, (a i) ^ 2) ≤ (R : ℝ) := ha.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR1 hK)
  have hmax : coordinateMax hn (fun i => |a i| / ψ i) ≤ (R : ℝ) * Q := by
    apply coordinateMax_le
    intro i
    have hai : |a i| ≤ Real.sqrt (∑ j, (a j) ^ 2) := by
      simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using
        PiLp.norm_apply_le (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n)) i
    rw [div_eq_mul_inv]
    exact mul_le_mul (hai.trans haR) (weighted_reciprocal_le Q hQ0 ψ hψ hψ1 hprod i)
      (inv_nonneg.mpr (hψ i).le) hR0.le
  have hp : 1 < (Real.log Q) ^ n := one_lt_pow₀ hlog (Nat.ne_of_gt hn)
  have hcoef : 1 < C₂ * (Real.log Q) ^ n := hp.trans_le
    (le_mul_of_one_le_left (by positivity) hC₂)
  have hh := mul_lt_mul_of_pos_left hcoef (mul_pos hR0 hQ0)
  nlinarith only [hh, hlarge.trans hmax]

/-- For every positive dimension, `K > 1`, any `C₁`, and any `C₂ > 0`, the
hypotheses have witnesses with arbitrarily large natural `R`. Equal tolerances
and a vector supported in one coordinate suffice. -/
theorem theoremTwo_admissible_exists (n : ℕ) (hn : 0 < n) (K : ℝ) (hK : 1 < K)
    (C₁ C₂ : ℝ) (hC₂ : 0 < C₂) (Rmin : ℕ) :
    ∃ (Q R : ℕ) (a ψ : Fin n → ℝ), Rmin ≤ R ∧
      TheoremTwoAdmissible n hn K C₁ C₂ Q R a ψ := by
  have hevent : ∀ᶠ Q : ℕ in Filter.atTop,
      C₂ * equalWeight n Q * (Real.log Q + 1) ^ n ≤ 1 :=
    tendsto_natCast_atTop_atTop.eventually (equalWeight_log_pow_small n hn C₂ n 1 zero_lt_one)
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp hevent
  let Q := max Q₀ (max 2 ⌈C₁⌉₊)
  have hQlower : C₁ ≤ (Q : ℝ) := (Nat.le_ceil C₁).trans (by
    exact_mod_cast (le_max_right 2 ⌈C₁⌉₊).trans (le_max_right Q₀ _))
  have hQ2 : (2 : ℝ) ≤ Q := by
    exact_mod_cast (le_max_left 2 ⌈C₁⌉₊).trans (le_max_right Q₀ _)
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlog0 : 0 < Real.log Q := Real.log_pos (by linarith)
  let ε := equalWeight n Q
  have hε : 0 < ε := equalWeight_pos n hQ0
  have hεupper : ε ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n := by
    have hsmall := hQ₀ Q (le_max_left _ _)
    have hp : (Real.log Q) ^ n ≤ (Real.log Q + 1) ^ n :=
      pow_le_pow_left₀ hlog0.le (by linarith) n
    have hh := (mul_le_mul_of_nonneg_left hp (show 0 ≤ C₂ * ε by positivity)).trans hsmall
    have ht : 0 < C₂ * (Real.log Q) ^ n := by positivity
    rw [inv_pow, ← mul_inv]
    rw [← one_div]
    apply (le_div_iff₀ ht).mpr
    nlinarith only [hh]
  let D := C₂ * Q * (Real.log Q) ^ n * ε
  have hD : 0 < D := by dsimp [D]; positivity
  have hgrow : ∀ᶠ R : ℕ in Filter.atTop, D ≤ (R : ℝ) ^ (K - 1) :=
    ((tendsto_rpow_atTop (sub_pos.mpr hK)).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop D)
  have hpower : ∀ᶠ R : ℕ in Filter.atTop, (Q : ℝ) ≤ (R : ℝ) ^ originalExponent K :=
    ((tendsto_rpow_atTop (originalExponent_pos K)).comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (Q : ℝ))
  obtain ⟨R, hgrow, hpower, hRmin, hRnat⟩ :=
    (hgrow.and (hpower.and ((Filter.eventually_ge_atTop Rmin).and
      (Filter.eventually_ge_atTop 1)))).exists
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hRnat
  let k : Fin n := ⟨0, hn⟩
  let a : Fin n → ℝ := Pi.single k (D * R)
  have hanorm : Real.sqrt (∑ i, (a i) ^ 2) = D * R := by
    simp [a, Pi.single_apply, apply_ite (fun x : ℝ => x ^ 2), Real.sqrt_sq,
      (mul_pos hD hR0).le]
  refine ⟨Q, R, a, (fun _ => ε), hRmin, hQlower, hpower, ?_,
    (fun _ => hε), (fun _ => hεupper), ?_, ?_⟩
  · rw [hanorm]
    calc
      D * R ≤ (R : ℝ) ^ (K - 1) * R := mul_le_mul_of_nonneg_right hgrow hR0.le
      _ = (R : ℝ) ^ K := by rw [← Real.rpow_add_one hR0.ne']; congr 1; ring
  · simpa using equalWeight_pow n hn hQ0
  · apply le_trans _ (le_coordinateMax hn (fun i => |a i| / ε) k)
    simp only [a, Pi.single_eq_same, abs_of_pos (mul_pos hD hR0)]
    dsimp [D]
    apply le_of_eq
    field_simp

end BakerHarman
