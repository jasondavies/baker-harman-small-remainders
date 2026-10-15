import BakerHarman.Lattice.Primitive

/-!
Adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Combinatorics/Progressions/Linear/NormalHyperplaneProjection.lean`.
The imports and namespace are reduced to this proof dependency.
Upstream code is licensed under Apache 2.0; see
`vendor/baker-harman-analytics/LICENSE`.
-/

namespace BakerHarman

section


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

theorem normalHyperplane_starProjection (ξ x : E) (hξ : ξ ≠ 0) :
    (normalFunctional ξ).ker.starProjection x =
      x - (inner ℝ ξ x / ‖ξ‖ ^ 2) • ξ := by
  have hn : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hξ)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change inner ℝ ξ (x - (inner ℝ ξ x / ‖ξ‖ ^ 2) • ξ) = 0
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ hn, sub_self]
  · intro y hy
    have hy' : inner ℝ ξ y = 0 := hy
    rw [sub_sub_cancel, real_inner_smul_left, hy', mul_zero]

theorem normalHyperplane_height (ξ w : E) (hξ : ξ ≠ 0)
    (hw : inner ℝ ξ w = 1) :
    ‖w - (normalFunctional ξ).ker.starProjection w‖ = ‖ξ‖⁻¹ := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  rw [normalHyperplane_starProjection ξ w hξ, sub_sub_cancel, hw,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp


/-- Exact size of the error when projecting onto a normal hyperplane. -/
theorem normalHyperplane_projection_error (ξ y : E) (hξ : ξ ≠ 0) :
    ‖y - (normalFunctional ξ).ker.starProjection y‖ = |inner ℝ ξ y| / ‖ξ‖ := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  rw [normalHyperplane_starProjection ξ y hξ, sub_sub_cancel, norm_smul,
    Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖ξ‖)]
  field_simp

/-- A lower bound on the projected vector, stated in the direction used by
lattice dimension induction. -/
theorem norm_le_normalHyperplane_projection_add (ξ y : E) (hξ : ξ ≠ 0) :
    ‖y‖ ≤ ‖(normalFunctional ξ).ker.starProjection y‖ + |inner ℝ ξ y| / ‖ξ‖ := by
  calc
    ‖y‖ ≤ ‖(normalFunctional ξ).ker.starProjection y‖ +
        ‖y - (normalFunctional ξ).ker.starProjection y‖ := by
          simpa only [norm_sub_rev] using norm_le_insert ((normalFunctional ξ).ker.starProjection y) y
    _ = _ := by rw [normalHyperplane_projection_error ξ y hξ]

/-- Approximating the projection and controlling its normal error gives an
approximation in the original space. -/
theorem reciprocal_normalHyperplane_transfer (ξ y m : E) (hξ : ξ ≠ 0)
    (r a b : ℝ) (hr : 0 < r)
    (happrox : ‖r⁻¹ • (normalFunctional ξ).ker.starProjection y - m‖ < a)
    (herror : |inner ℝ ξ y| / ‖ξ‖ ≤ r * b) :
    ‖r⁻¹ • y - m‖ < a + b := by
  have he : ‖r⁻¹ • (y - (normalFunctional ξ).ker.starProjection y)‖ ≤ b := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
      normalHyperplane_projection_error ξ y hξ]
    exact (inv_mul_le_iff₀ hr).mpr herror
  calc
    _ = ‖(r⁻¹ • (normalFunctional ξ).ker.starProjection y - m) +
        r⁻¹ • (y - (normalFunctional ξ).ker.starProjection y)‖ := by
      congr 1; simp only [smul_sub]; abel
    _ ≤ ‖r⁻¹ • (normalFunctional ξ).ker.starProjection y - m‖ +
        ‖r⁻¹ • (y - (normalFunctional ξ).ker.starProjection y)‖ := norm_add_le _ _
    _ < a + b := add_lt_add_of_lt_of_le happrox he

/-- A nonzero normal always cuts the dimension down by one. -/
theorem normalHyperplane_finrank (ξ : E) (hξ : ξ ≠ 0) :
    Module.finrank ℝ (normalFunctional ξ).ker + 1 = Module.finrank ℝ E := by
  apply OAI.Erdos3.hyperplane_finrank (normalFunctional ξ) ((‖ξ‖ ^ 2)⁻¹ • ξ)
  simp only [normalFunctional_apply, inner_smul_right, real_inner_self_eq_norm_sq]
  exact inv_mul_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hξ))

/-- In dimension one the normal component is the whole vector. -/
theorem norm_eq_abs_inner_div_norm_of_finrank_one (hdim : Module.finrank ℝ E = 1)
    (ξ y : E) (hξ : ξ ≠ 0) : ‖y‖ = |inner ℝ ξ y| / ‖ξ‖ := by
  have hr := normalHyperplane_finrank ξ hξ
  have hk : (normalFunctional ξ).ker = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  simpa only [hk, Submodule.starProjection_bot, zero_apply, sub_zero] using
    normalHyperplane_projection_error ξ y hξ

end

end BakerHarman
