import BakerHarman.SmallVector
import BakerHarman.EqualWeightBudget

/-!
# Equal-weight approximation for small vectors

The two thresholds absorb the logarithmic size bound and the reciprocal
rounding error. The original power range is retained.
-/

namespace BakerHarman

theorem small_vector_equal_weights (n : ℕ) (hn : 2 ≤ n) (K A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ Q₀ R₀ : ℝ, 1 ≤ Q₀ ∧ 5 ≤ R₀ ∧ ∀ Q R : ℝ, Q₀ ≤ Q → R₀ ≤ R →
      Q ≤ R ^ gammaBH K → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) →
      (∀ i, a i ≤ A * equalWeight n Q * R * Q * (Real.log Q + 1) ^ m) →
      ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧
        ∀ i, distNearestInt (a i / r) ≤ equalWeight n Q := by
  obtain ⟨s, hs0, hs1, hbudget⟩ := equalWeight_dirichlet_budget n hn
  obtain ⟨q₁, hbudget⟩ := Filter.eventually_atTop.mp hbudget
  obtain ⟨q₂, hsize⟩ := Filter.eventually_atTop.mp
    (equalWeight_log_pow_small n (by omega) A m 1 (by norm_num))
  obtain ⟨r₁, hround⟩ := Filter.eventually_atTop.mp
    (log_product_power_range_small K A hA.le m (1 - s) (sub_pos.mpr hs1))
  refine ⟨max 1 (max q₁ q₂), max 5 r₁, le_max_left _ _, le_max_left _ _, ?_⟩
  intro Q R hQ hR hQR a ha hsmall
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := by linarith
  have hR5 : 5 ≤ R := (le_max_left _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hψ : 0 < equalWeight n Q := equalWeight_pos n hQ0
  obtain ⟨M, hM, hden, hacc⟩ := hbudget Q ((le_max_left _ _).trans ((le_max_right _ _).trans hQ))
  have hsize := hsize Q ((le_max_right _ _).trans ((le_max_right _ _).trans hQ))
  have hround := hround R ((le_max_right _ _).trans hR) Q hQ1 hQR
  apply small_vector_reciprocal (by omega) a ha R Q (equalWeight n Q) hR5 hQ1 hψ M hM hden
  · intro i
    have h := mul_le_mul_of_nonneg_right hsize (mul_nonneg hR0.le hQ0.le)
    nlinarith only [hsmall i, h]
  · intro i
    have he : a i / R ^ 2 ≤ (1 - s) * equalWeight n Q := by
      apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
      have h := mul_le_mul_of_nonneg_left hround (show 0 ≤ equalWeight n Q * R by positivity)
      nlinarith only [hsmall i, h]
    nlinarith only [hacc, he]

end BakerHarman
