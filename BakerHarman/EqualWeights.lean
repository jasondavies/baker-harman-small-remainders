import BakerHarman.DimensionInduction
import BakerHarman.SmallVectorEqualWeights
import BakerHarman.Lattice.CoordinateLattice

/-!
# Unconditional reciprocal approximation with equal weights

The large-vector lattice induction and the small-vector Dirichlet argument cover
all nonnegative vectors. Equal coordinate weights absorb the logarithmic losses
without changing `gammaBH` or the modulus interval `[R, 2QR]`.
-/

namespace BakerHarman

/-- Equal-weight form of the reciprocal approximation used in Theorem 1.
There are no analytic or lattice hypotheses: all constants depend only on `n,K`. -/
theorem bakerHarman_equal_weights (n : ℕ) (hn : 2 ≤ n) (K : ℝ) (hK : 1 ≤ K) :
    ∃ Q₀ R₀ : ℝ, 1 ≤ Q₀ ∧ 5 ≤ R₀ ∧ ∀ Q R : ℝ, Q₀ ≤ Q → R₀ ≤ R →
      Q ≤ R ^ gammaBH K → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) →
      Real.sqrt (∑ i, (a i) ^ 2) ≤ R ^ K →
      ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧
        ∀ i, distNearestInt (a i / r) ≤ equalWeight n Q := by
  obtain ⟨m, A, B, Ql, Rl, hA, hB, hQl, hRl, hlattice⟩ :=
    bakerHarman_lattice_approximation n (by omega) K hK
  obtain ⟨Qs, Rs, hQs, hRs, hsmall⟩ := small_vector_equal_weights n hn K A hA (m + 1)
  obtain ⟨q₁, hbig⟩ := Filter.eventually_atTop.mp
    (equalWeight_log_pow_small n (by omega) B m 2 (by norm_num))
  refine ⟨max Ql (max Qs q₁), max Rl Rs, hQl.trans (le_max_left _ _),
    hRs.trans (le_max_right _ _), ?_⟩
  intro Q R hQ hR hQR a ha hy
  have hQlQ : Ql ≤ Q := (le_max_left _ _).trans hQ
  have hQsQ : Qs ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hq₁Q : q₁ ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hQ1 : 1 ≤ Q := hQl.trans hQlQ
  have hQ0 : 0 < Q := by linarith
  have hRlR : Rl ≤ R := (le_max_left _ _).trans hR
  have hRsR : Rs ≤ R := (le_max_right _ _).trans hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  let E := EuclideanSpace ℝ (Fin n)
  let x : E := WithLp.toLp 2 a
  let ψ := equalWeight n Q
  let ρ := ψ⁻¹
  have hψ : 0 < ψ := equalWeight_pos n hQ0
  have hρ : 0 < ρ := inv_pos.mpr hψ
  have hρ1 : 1 ≤ ρ := (one_le_inv₀ hψ).mpr (equalWeight_le_one n hQ1)
  have hρψ : ρ⁻¹ = ψ := inv_inv ψ
  have hρpow : ρ ^ n = Q := by
    dsimp only [ρ, ψ]
    rw [inv_pow, equalWeight_pow n (by omega) hQ0, inv_inv]
  have hρQ : ρ ≤ Q := by
    rw [show ρ = Q ^ (n : ℝ)⁻¹ from equalWeight_inv n hQ0.le]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ1
      (inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ n by omega)))
  have hQR' : Q ≤ R := hQR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR1
      (show gammaBH K ≤ 1 by linarith [gammaBH_le K]))
  have hx : ‖x‖ ≤ R ^ K := by
    have he : ‖x‖ = Real.sqrt (∑ i, (a i) ^ 2) := by
      simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq x
    rw [he]
    exact hy
  let Λ := scaledLattice (coordinateLattice (Fin n)) ρ hρ.ne'
  have hsep : ∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖ := by
    simpa only [mul_one] using scaledLattice_separation (coordinateLattice (Fin n)) ρ hρ 1
      (coordinateLattice_separation (Fin n))
  have hcov : ZLattice.covolume Λ = Q := by
    dsimp only [Λ]
    rw [scaledLattice_covolume _ ρ hρ, finrank_euclideanSpace_fin,
      coordinateLattice_covolume, mul_one, hρpow]
  have hyupper : ‖ρ • x‖ ≤ R ^ (K + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    calc
      _ ≤ R * R ^ K := mul_le_mul (hρQ.trans hQR') hx (norm_nonneg _) hR0.le
      _ = _ := by rw [Real.rpow_add hR0, Real.rpow_one]; ring
  by_cases hlarge : A * R * Q * (Real.log Q + 1) ^ (m + 1) ≤ ‖ρ • x‖
  · obtain ⟨r, hr, hrupper, v, hv⟩ := hlattice R hRlR Q hQlQ hQR E
      finrank_euclideanSpace_fin Λ ρ hρ1 hsep hcov.le (ρ • x) hlarge hyupper
    have hrnonneg : (0 : ℤ) ≤ r := by exact_mod_cast (hR0.le.trans hr)
    have her : (r.toNat : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hrnonneg
    refine ⟨r.toNat, by simpa only [her] using hr, ?_, ?_⟩
    · rw [her]
      apply hrupper.trans
      rw [div_eq_mul_inv, hρψ]
      have hh := mul_le_mul_of_nonneg_right (hbig Q hq₁Q) (show 0 ≤ R * Q by positivity)
      nlinarith only [hh]
    · have hcoords := coordinateLattice_reciprocal_approximation (Fin n) ρ hρ r x ⟨v, hv⟩
      intro i
      simpa only [her, hρψ] using hcoords i
  · apply hsmall Q R hQsQ hRsR hQR a ha
    intro i
    have hi : a i ≤ ‖x‖ := by
      have hh : ‖a i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ha i)] using hh
    have hlo : ρ * ‖x‖ ≤ A * R * Q * (Real.log Q + 1) ^ (m + 1) := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hρ] using (le_of_not_ge hlarge)
    have h := mul_le_mul_of_nonneg_left hlo hψ.le
    have he : ψ * (ρ * ‖x‖) = ‖x‖ := by rw [← mul_assoc, mul_inv_cancel₀ hψ.ne', one_mul]
    rw [he] at h
    nlinarith only [hi, h]

end BakerHarman
