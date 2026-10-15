import BakerHarman.EqualWeightBudget
import BakerHarman.WeightedSmallVector

/-! Uniform rounding budgets for unequal coordinate tolerances. -/

namespace BakerHarman

/-- The product of all tolerances except the selected coordinate. -/
lemma weighted_remaining_product {n : ℕ} (ψ : Fin n → ℝ) (k : Fin n)
    (Q : ℝ) (hQ : Q ≠ 0) (hprod : ∏ i, ψ i = Q⁻¹) :
    (∏ i : {i : Fin n // i ≠ k}, ψ i) * (Q * ψ k) = 1 := by
  classical
  have hp : (∏ i : {i : Fin n // i ≠ k}, ψ i) * ψ k = Q⁻¹ := by
    rw [← Finset.prod_subtype (Finset.univ.erase k) (by simp) ψ]
    exact (Finset.prod_erase_mul Finset.univ ψ (Finset.mem_univ k)).trans hprod
  calc
    _ = ((∏ i : {i : Fin n // i ≠ k}, ψ i) * ψ k) * Q := by ring
    _ = 1 := by rw [hp, inv_mul_cancel₀ hQ]

/-- Uniform error margin for rectangular Dirichlet boxes. -/
theorem weighted_dirichlet_budget (n : ℕ) (hn : 0 < n) :
    ∃ s τ : ℝ, 0 < s ∧ s < 1 ∧ 0 < τ ∧ ∀ (Q : ℝ) (ψ : Fin n → ℝ),
      0 < Q → (∀ i, 0 < ψ i) → (∀ i, ψ i ≤ τ) → (∏ i, ψ i) = Q⁻¹ →
      ∃ M : Fin n → ℕ, (∀ i, 0 < M i) ∧
        (∀ k, (∏ i : {i : Fin n // i ≠ k}, (M i : ℝ)) ≤ (5 / 4 : ℝ) * Q * ψ k) ∧
        (∀ i, 1 / (M i : ℝ) ≤ s * ψ i) := by
  classical
  let d := n
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
  refine ⟨α⁻¹, β - α, inv_pos.mpr hα0, inv_lt_one_of_one_lt₀ hα,
    sub_pos.mpr hαβ, ?_⟩
  intro Q ψ hQ hψ hsmall hprod
  let M : Fin n → ℕ := fun i => ⌈α / ψ i⌉₊
  have hM (i) : 0 < M i := Nat.ceil_pos.mpr (div_pos hα0 (hψ i))
  have hM0 (i) : (0 : ℝ) < M i := by exact_mod_cast hM i
  have hMlo (i) : α / ψ i ≤ M i := Nat.le_ceil _
  have hMψ (i) : (M i : ℝ) * ψ i ≤ β := by
    have hMhi : (M i : ℝ) < α / ψ i + 1 := Nat.ceil_lt_add_one (by positivity [hψ i])
    have he : (α / ψ i + 1) * ψ i = α + ψ i := by field_simp [(hψ i).ne']
    have hh := mul_lt_mul_of_pos_right hMhi (hψ i)
    rw [he] at hh
    linarith [hsmall i]
  refine ⟨M, hM, ?_, ?_⟩
  · intro k
    let I := {i : Fin n // i ≠ k}
    have hcard : Fintype.card I = n - 1 := by
      dsimp [I, d]
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
    have hp : (∏ i : I, (M i : ℝ) * ψ i) ≤ β ^ d := by
      calc
        _ ≤ ∏ _i : I, β := Finset.prod_le_prod₀ (fun i _ => by positivity [hM0 i, hψ i]) (fun i _ => hMψ i)
        _ = β ^ (n - 1) := by simp [hcard]
        _ ≤ β ^ d := pow_le_pow_right₀ (by linarith) (by dsimp [d]; omega)
    rw [Finset.prod_mul_distrib, hβpow] at hp
    have hh := mul_le_mul_of_nonneg_right hp (show 0 ≤ Q * ψ k by positivity [hψ k])
    have he := weighted_remaining_product ψ k Q hQ.ne' hprod
    have hr : ((∏ i : I, (M i : ℝ)) * ∏ i : I, ψ i) * (Q * ψ k) =
        ∏ i : I, (M i : ℝ) := by rw [mul_assoc, he, mul_one]
    rw [hr] at hh
    simpa only [mul_assoc] using hh
  · intro i
    have hαM : α ≤ (M i : ℝ) * ψ i := (div_le_iff₀ (hψ i)).mp (hMlo i)
    apply (div_le_iff₀ (hM0 i)).mpr
    have hh := mul_le_mul_of_nonneg_left hαM (inv_pos.mpr hα0).le
    rw [inv_mul_cancel₀ hα0.ne'] at hh
    nlinarith only [hh]

/-- The small-vector case with the logarithmic coordinate restrictions. -/
theorem bakerHarman_weighted_small_vector (n : ℕ) (hn : 0 < n) (K A : ℝ)
    (hA : 0 < A) (m : ℕ) :
    ∃ c R₀ : ℝ, 0 < c ∧ 5 ≤ R₀ ∧ ∀ Q R : ℝ, 1 ≤ Q → R₀ ≤ R →
      Q ≤ R ^ gammaBH K → ∀ (a ψ : Fin n → ℝ), (∀ i, 0 ≤ a i) →
      (∀ i, 0 < ψ i) → (∀ i, ψ i ≤ c / (Real.log Q + 1) ^ m) →
      (∏ i, ψ i) = Q⁻¹ →
      (∀ i, a i ≤ A * ψ i * R * Q * (Real.log Q + 1) ^ m) →
      ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨s, τ, hs0, hs1, hτ, hbudget⟩ := weighted_dirichlet_budget n hn
  obtain ⟨r₁, hround⟩ := Filter.eventually_atTop.mp
    (log_product_power_range_small K A hA.le m (1 - s) (sub_pos.mpr hs1))
  let c := min τ A⁻¹
  have hc : 0 < c := lt_min hτ (inv_pos.mpr hA)
  refine ⟨c, max 5 r₁, hc, le_max_left _ _, ?_⟩
  intro Q R hQ hR hQR a ψ ha hψ hψupper hprod hsmall
  have hQ0 : 0 < Q := by linarith
  have hR5 : 5 ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hL1 : 1 ≤ Real.log Q + 1 := by linarith [Real.log_nonneg hQ]
  have hLpow : 1 ≤ (Real.log Q + 1) ^ m := one_le_pow₀ hL1
  have hLpos : 0 < (Real.log Q + 1) ^ m := by linarith
  have hψc (i) : ψ i * (Real.log Q + 1) ^ m ≤ c :=
    (le_div_iff₀ hLpos).mp (hψupper i)
  have hψτ (i) : ψ i ≤ τ := by
    have hh := mul_le_mul_of_nonneg_left hLpow (hψ i).le
    have hcτ : c ≤ τ := min_le_left _ _
    nlinarith only [hh, hψc i, hcτ]
  obtain ⟨M, hM, hden, hacc⟩ := hbudget Q ψ hQ0 hψ hψτ hprod
  apply small_vector_weighted_reciprocal (by omega) a ha R Q ψ hR5 hQ hψ M hM hden
  · intro i
    have hcA : A * c ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (min_le_right τ A⁻¹) hA.le
      simpa only [mul_inv_cancel₀ hA.ne'] using hh
    have hcoef : A * ψ i * (Real.log Q + 1) ^ m ≤ 1 := by
      nlinarith only [mul_le_mul_of_nonneg_left (hψc i) hA.le, hcA]
    have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ R * Q by positivity)
    nlinarith only [hsmall i, hh]
  · intro i
    have hr := hround R ((le_max_right _ _).trans hR) Q hQ hQR
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ ψ i * R by positivity [hψ i])
    have he : a i / R ^ 2 ≤ (1 - s) * ψ i := by
      apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
      nlinarith only [hsmall i, hh]
    nlinarith only [he, hacc i]

end BakerHarman
