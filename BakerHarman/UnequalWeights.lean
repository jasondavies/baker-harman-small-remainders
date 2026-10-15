import BakerHarman.SharpDimensionInduction
import BakerHarman.WeightedBudget
import BakerHarman.Lattice.WeightedCoordinateLattice

/-!
# Unequal-weight small remainders

The sharp logarithmic lattice induction and rectangular Dirichlet approximation
cover the large and small weighted-vector cases, respectively.
-/

namespace BakerHarman

lemma weighted_reciprocal_le {n : ℕ} (Q : ℝ) (hQ : 0 < Q)
    (ψ : Fin n → ℝ) (hψ : ∀ i, 0 < ψ i) (hψ1 : ∀ i, ψ i ≤ 1)
    (hprod : ∏ i, ψ i = Q⁻¹) (i : Fin n) : (ψ i)⁻¹ ≤ Q := by
  classical
  have hp : (∏ j : {j : Fin n // j ≠ i}, ψ j) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => (hψ j).le) (fun j _ => hψ1 j)
  have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ Q * ψ i by positivity [hψ i])
  rw [weighted_remaining_product ψ i Q hQ.ne' hprod, one_mul] at hh
  rw [← one_div]
  exact (div_le_iff₀ (hψ i)).mpr hh

lemma weighted_norm_le {n : ℕ} (a ψ : Fin n → ℝ) (hψ : ∀ i, 0 < ψ i)
    (Q : ℝ) (hQ : 0 ≤ Q) (hbound : ∀ i, (ψ i)⁻¹ ≤ Q) :
    ‖(WithLp.toLp 2 (fun i => a i / ψ i) : EuclideanSpace ℝ (Fin n))‖ ≤
      Q * ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hQ (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change (a i / ψ i) ^ 2 ≤ Q ^ 2 * (a i) ^ 2
  have hh := mul_le_mul_of_nonneg_left (hbound i) (abs_nonneg (a i))
  have he : |a i / ψ i| ≤ Q * |a i| := by
    rw [abs_div, abs_of_pos (hψ i), div_eq_mul_inv]
    nlinarith only [hh]
  have hsq := pow_le_pow_left₀ (abs_nonneg (a i / ψ i)) he 2
  simpa only [sq_abs, mul_pow] using hsq

/-- Full unequal-weight approximation with `log Q + 1`, for nonnegative real
vectors. The stronger shifted-sets power exponent is retained. -/
theorem bakerHarman_unequal_weights_nonneg (n : ℕ) (hn : 0 < n) (K : ℝ) (hK : 1 ≤ K) :
    ∃ c Q₀ R₀ : ℝ, 0 < c ∧ 1 ≤ Q₀ ∧ 5 ≤ R₀ ∧ ∀ Q R : ℝ, Q₀ ≤ Q → R₀ ≤ R →
      Q ≤ R ^ gammaBH K → ∀ a ψ : Fin n → ℝ, (∀ i, 0 ≤ a i) →
      Real.sqrt (∑ i, (a i) ^ 2) ≤ R ^ K → (∀ i, 0 < ψ i) →
      (∀ i, ψ i ≤ c / (Real.log Q + 1) ^ n) → (∏ i, ψ i) = Q⁻¹ →
      ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨A, B, Ql, Rl, hA, hB, hQl, hRl, hlattice⟩ :=
    bakerHarman_sharp_lattice_approximation n (by omega) K hK (gammaBH K)
      (gammaBH_pos K) (gammaBH_lt_analyticPowerRange K)
  obtain ⟨cs, Rs, hcs, hRs, hsmall⟩ := bakerHarman_weighted_small_vector n hn K A hA n
  let c := min cs (min 1 B⁻¹)
  have hc : 0 < c := lt_min hcs (lt_min zero_lt_one (inv_pos.mpr hB))
  have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hcB : c * B ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right
      ((min_le_right cs (min 1 B⁻¹)).trans (min_le_right 1 B⁻¹)) hB.le
    simpa only [inv_mul_cancel₀ hB.ne'] using hh
  refine ⟨c, Ql, max Rl Rs, hc, hQl, hRs.trans (le_max_right _ _), ?_⟩
  intro Q R hQ hR hQR a ψ ha hy hψ hψupper hprod
  have hQ1 : 1 ≤ Q := hQl.trans hQ
  have hQ0 : 0 < Q := by linarith
  have hRlR : Rl ≤ R := (le_max_left _ _).trans hR
  have hRsR : Rs ≤ R := (le_max_right _ _).trans hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  let L := Real.log Q + 1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hQ1]
  have hLn : 0 < L ^ n := pow_pos (by linarith) _
  have hLnp : 1 ≤ L ^ n := one_le_pow₀ hL1
  have hψc (i) : ψ i * L ^ n ≤ c := (le_div_iff₀ hLn).mp (hψupper i)
  have hψ1 (i) : ψ i ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hLnp (hψ i).le
    nlinarith only [hh, hψc i, hc1]
  let E := EuclideanSpace ℝ (Fin n)
  let x : E := WithLp.toLp 2 a
  let y : E := WithLp.toLp 2 (fun i => a i / ψ i)
  let ρ := L ^ n / c
  have hρ1 : 1 ≤ ρ := (le_div_iff₀ hc).mpr (by nlinarith only [hc1, hLnp])
  have hρ0 : 0 < ρ := by linarith
  let Λ := weightedCoordinateLattice ψ hψ
  have hsep : ∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖ := by
    apply weightedCoordinateLattice_separation ψ hψ ρ hρ0.le
    intro i
    dsimp [ρ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hc).mpr
    simpa only [one_mul, mul_comm] using hψc i
  have hcov : ZLattice.covolume Λ = Q := by
    rw [weightedCoordinateLattice_covolume, hprod, inv_inv]
  have hx : ‖x‖ ≤ R ^ K := by
    have he : ‖x‖ = Real.sqrt (∑ i, (a i) ^ 2) := by
      simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq x
    rwa [he]
  have hQR' : Q ≤ R := hQR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR1
      (show gammaBH K ≤ 1 by linarith [gammaBH_le K]))
  have hyupper : ‖y‖ ≤ R ^ (K + 1) := by
    have hh := weighted_norm_le a ψ hψ Q hQ0.le (weighted_reciprocal_le Q hQ0 ψ hψ hψ1 hprod)
    calc
      ‖y‖ ≤ Q * ‖x‖ := hh
      _ ≤ R * R ^ K := mul_le_mul hQR' hx (norm_nonneg _) hR0.le
      _ = _ := by rw [Real.rpow_add hR0, Real.rpow_one]; ring
  by_cases hlarge : A * R * Q * L ^ n ≤ ‖y‖
  · obtain ⟨r, hr, hrupper, v, hv⟩ := hlattice R hRlR Q hQ hQR E
      finrank_euclideanSpace_fin Λ ρ hρ1 hsep hcov.le y
      (by simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hlarge) hyupper
    have hrnonneg : (0 : ℤ) ≤ r := by exact_mod_cast (hR0.le.trans hr)
    have her : (r.toNat : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hrnonneg
    refine ⟨r.toNat, by simpa only [her] using hr, ?_, ?_⟩
    · rw [her]
      apply hrupper.trans
      have hpow : L ^ (n - 1) ≤ L ^ n := pow_le_pow_right₀ hL1 (by omega)
      have hcoef : B * L ^ (n - 1) ≤ ρ := by
        apply (le_div_iff₀ hc).mpr
        have hh := mul_le_mul_of_nonneg_left hpow (mul_nonneg hB.le hc.le)
        have hh' := mul_le_mul_of_nonneg_right hcB hLn.le
        nlinarith only [hh, hh']
      apply (div_le_iff₀ hρ0).mpr
      have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ R * Q by positivity)
      nlinarith only [hh, mul_nonneg (mul_nonneg hR0.le hQ0.le) hρ0.le]
    · have hh := weightedCoordinateLattice_reciprocal_approximation ψ hψ r a ⟨v, hv⟩
      simpa only [her] using hh
  · apply hsmall Q R hQ1 hRsR hQR a ψ ha hψ
    · intro i
      exact (hψupper i).trans (div_le_div_of_nonneg_right (min_le_left _ _) hLn.le)
    · exact hprod
    · intro i
      have hi : a i / ψ i ≤ ‖y‖ := by
        have hh := PiLp.norm_apply_le y i
        change |a i / ψ i| ≤ ‖y‖ at hh
        rwa [abs_of_nonneg (div_nonneg (ha i) (hψ i).le)] at hh
      have hh : a i / ψ i ≤ A * R * Q * L ^ n := hi.trans (le_of_not_ge hlarge)
      have hm := (div_le_iff₀ (hψ i)).mp hh
      nlinarith only [hm]

lemma distNearestInt_neg (x : ℝ) : distNearestInt (-x) = distNearestInt x := by
  have h (x : ℝ) : distNearestInt (-x) ≤ distNearestInt x := by
    have hh := round_le (-x) (-round x)
    have he : -x - ((-round x : ℤ) : ℝ) = -(x - (round x : ℝ)) := by
      push_cast; ring
    rw [he, abs_neg] at hh
    exact hh
  exact le_antisymm (h x) (by simpa only [neg_neg] using h (-x))

lemma distNearestInt_abs (x : ℝ) : distNearestInt |x| = distNearestInt x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, distNearestInt_neg]

/-- Unequal-weight approximation for arbitrary real vectors and every growth
exponent. The logarithmic condition is written with `log Q + 1` for this version. -/
theorem bakerHarman_unequal_weights (n : ℕ) (hn : 0 < n) (K : ℝ) :
    ∃ c Q₀ R₀ : ℝ, 0 < c ∧ 1 ≤ Q₀ ∧ 5 ≤ R₀ ∧ ∀ Q R : ℝ, Q₀ ≤ Q → R₀ ≤ R →
      Q ≤ R ^ gammaBH K → ∀ a ψ : Fin n → ℝ,
      Real.sqrt (∑ i, (a i) ^ 2) ≤ R ^ K → (∀ i, 0 < ψ i) →
      (∀ i, ψ i ≤ c / (Real.log Q + 1) ^ n) → (∏ i, ψ i) = Q⁻¹ →
      ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨c, Q₀, R₀, hc, hQ₀, hR₀, h⟩ :=
    bakerHarman_unequal_weights_nonneg n hn (max 1 K) (le_max_left _ _)
  refine ⟨c, Q₀, R₀, hc, hQ₀, hR₀, ?_⟩
  intro Q R hQ hR hQR a ψ ha hψ hψupper hprod
  have hR1 : 1 ≤ R := by linarith
  have he : gammaBH (max 1 K) = gammaBH K := by simp [gammaBH]
  obtain ⟨r, hr, hrupper, herr⟩ := h Q R hQ hR (by rwa [he]) (fun i => |a i|) ψ
    (fun _ => abs_nonneg _) (by
      simp only [sq_abs]
      exact ha.trans (Real.rpow_le_rpow_of_exponent_le hR1 (le_max_right _ _)))
    hψ hψupper hprod
  refine ⟨r, hr, hrupper, fun i => ?_⟩
  have hi := distNearestInt_abs (a i / r)
  rw [abs_div, show |(r : ℝ)| = (r : ℝ) from abs_of_nonneg (Nat.cast_nonneg r)] at hi
  rw [← hi]
  exact herr i

end BakerHarman
