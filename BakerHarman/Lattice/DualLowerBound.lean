import BakerHarman.Lattice.SeparatedMass

/-!
# Lower bounds for nonzero dual vectors

The Gaussian mass estimate along multiples is adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Combinatorics/Progressions/Estimates/GaussianScaledShortVectorBound.lean`.
Upstream code is licensed under Apache 2.0; see
`vendor/baker-harman-analytics/LICENSE`.
-/

namespace BakerHarman

open OAI.Erdos3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem latticeGaussianMass_ge_multiples_at_temperature
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0)
    {t : ℝ} (ht : 0 < t) (M : ℕ) (hM : (M : ℝ) * (Real.sqrt t * ‖ξ‖) ≤ 1) :
    ((M : ℝ) + 1) * Real.exp (-Real.pi) ≤ latticeGaussianMass Λ t 0 := by
  classical
  let v : ℕ → Λ := fun n => n • (⟨ξ, hξΛ⟩ : Λ)
  have hv (n : ℕ) : (v n : E) = (n : ℝ) • ξ := by
    rw [Nat.cast_smul_eq_nsmul]
    exact map_nsmul Λ.subtype n ⟨ξ, hξΛ⟩
  have hinj : Function.Injective v := by
    intro n m h
    have he := congrArg (fun x : Λ => (x : E)) h
    rw [hv, hv] at he
    exact Nat.cast_injective (smul_left_injective ℝ hξ he)
  have hterm (n : ℕ) (hn : n ∈ Finset.range (M + 1)) :
      Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * t * ‖(0 : E) - (v n : E)‖ ^ 2) := by
    have hnM : (n : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hnorm : Real.sqrt t * ‖(0 : E) - (v n : E)‖ ≤ 1 := by
      rw [zero_sub, norm_neg, hv, norm_smul, Real.norm_natCast]
      calc
        _ = (n : ℝ) * (Real.sqrt t * ‖ξ‖) := by ring
        _ ≤ (M : ℝ) * (Real.sqrt t * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right hnM (by positivity)
        _ ≤ 1 := hM
    have hsq := pow_le_one₀ (by positivity : 0 ≤ Real.sqrt t * ‖(0 : E) - (v n : E)‖) hnorm (n := 2)
    rw [mul_pow, Real.sq_sqrt ht.le] at hsq
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsq)]
  have hsum := Finset.sum_le_sum hterm
  have hbound := (lattice_gaussian_summable Λ ht 0).sum_le_tsum
    ((Finset.range (M + 1)).image v) (fun _ _ => (Real.exp_pos _).le)
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h)] at hbound
  have hcount : (∑ _n ∈ Finset.range (M + 1), Real.exp (-Real.pi)) =
      ((M : ℝ) + 1) * Real.exp (-Real.pi) := by simp
  rw [hcount] at hsum
  exact hsum.trans hbound

theorem latticeGaussianMass_mul_scaled_norm_ge
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (ξ : E) (hξΛ : ξ ∈ Λ) (hξ : ξ ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    Real.exp (-Real.pi) ≤ (Real.sqrt t * ‖ξ‖) * latticeGaussianMass Λ t 0 := by
  have hn : 0 < Real.sqrt t * ‖ξ‖ := mul_pos (Real.sqrt_pos.mpr ht) (norm_pos_iff.mpr hξ)
  let M := ⌊(Real.sqrt t * ‖ξ‖)⁻¹⌋₊
  have hM : (M : ℝ) * (Real.sqrt t * ‖ξ‖) ≤ 1 := by
    calc
      _ ≤ (Real.sqrt t * ‖ξ‖)⁻¹ * (Real.sqrt t * ‖ξ‖) :=
        mul_le_mul_of_nonneg_right (Nat.floor_le (inv_nonneg.mpr hn.le)) hn.le
      _ = 1 := inv_mul_cancel₀ hn.ne'
  have hmass := latticeGaussianMass_ge_multiples_at_temperature Λ ξ hξΛ hξ ht M hM
  have hlarge : 1 ≤ (Real.sqrt t * ‖ξ‖) * ((M : ℝ) + 1) := by
    have h := mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (Real.sqrt t * ‖ξ‖)⁻¹).le hn.le
    rw [mul_inv_cancel₀ hn.ne'] at h
    exact h
  calc
    _ ≤ ((Real.sqrt t * ‖ξ‖) * ((M : ℝ) + 1)) * Real.exp (-Real.pi) :=
      le_mul_of_one_le_left (Real.exp_pos _).le hlarge
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hmass hn.le]


section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Separation of a full lattice bounds each nonzero dual vector from below
in terms of the covolume, with a constant depending only on dimension. -/
theorem dual_norm_mul_covolume_lower_bound (Λ : Submodule ℤ F) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hsep : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖)
    (ξ : F) (hξΛ : ξ ∈ euclideanDualLattice Λ) (hξ : ξ ≠ 0) :
    Real.exp (-Real.pi) / (2 * (Real.sqrt (8 * ((Module.finrank ℝ F : ℝ) + 1))) ^
      Module.finrank ℝ F) ≤ ‖ξ‖ * ZLattice.covolume Λ := by
  let T : ℝ := 8 * ((Module.finrank ℝ F : ℝ) + 1)
  have hT : 0 < T := by dsimp [T]; positivity
  have hT1 : 1 ≤ T := by dsimp [T]; have := Nat.cast_nonneg (Module.finrank ℝ F) (α := ℝ); linarith
  have hmass := latticeGaussianMass_le_two_of_separated Λ T le_rfl hsep
  have hdual : latticeGaussianMass (euclideanDualLattice Λ) 1 0 ≤
      2 * (Real.sqrt T) ^ Module.finrank ℝ F * ZLattice.covolume Λ := by
    calc
      _ ≤ latticeGaussianMass (euclideanDualLattice Λ) T⁻¹ 0 :=
        latticeGaussianMass_antitone _ (inv_pos.mpr hT) (inv_le_one_of_one_le₀ hT1) 0
      _ = normalizedLatticeGaussian Λ T 0 := (normalizedLatticeGaussian_zero_eq_dual Λ hT).symm
      _ ≤ _ := by
        change ((Real.sqrt T) ^ Module.finrank ℝ F * ZLattice.covolume Λ) *
          latticeGaussianMass Λ T 0 ≤ _
        have h := mul_le_mul_of_nonneg_left hmass (latticeGaussianNormalizer_nonneg Λ T)
        dsimp only [latticeGaussianNormalizer] at h
        nlinarith [h]
  have hsmall := latticeGaussianMass_mul_scaled_norm_ge (euclideanDualLattice Λ) ξ hξΛ hξ
    (show (0 : ℝ) < 1 by norm_num)
  simp only [Real.sqrt_one, one_mul] at hsmall
  apply (div_le_iff₀ (by positivity : 0 < 2 * (Real.sqrt T) ^ Module.finrank ℝ F)).mpr
  calc
    _ ≤ ‖ξ‖ * latticeGaussianMass (euclideanDualLattice Λ) 1 0 := hsmall
    _ ≤ ‖ξ‖ * (2 * (Real.sqrt T) ^ Module.finrank ℝ F * ZLattice.covolume Λ) :=
      mul_le_mul_of_nonneg_left hdual (norm_nonneg ξ)
    _ = _ := by ring

end InnerProduct

end BakerHarman
