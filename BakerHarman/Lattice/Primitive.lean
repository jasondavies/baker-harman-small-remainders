import BakerHarman.Lattice.Dual

/-!
# Primitive dual vectors

The primitive normal construction is adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Combinatorics/Progressions/Lattices/NormalizedLatticeSheet.lean`.
The normal functional is the definition from `Estimates/IntegralHyperplaneCorrection.lean`.
Upstream code is licensed under Apache 2.0; see
`vendor/baker-harman-analytics/LICENSE`.
-/

namespace BakerHarman

open OAI.Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def normalFunctional (ξ : E) : E →ₗ[ℝ] ℝ := (innerSL ℝ ξ).toLinearMap

@[simp] theorem normalFunctional_apply (ξ x : E) : normalFunctional ξ x = inner ℝ ξ x := rfl

theorem exists_primitive_lattice_normal (Λ : Submodule ℤ E)
    (hspan : Submodule.span ℝ (Λ : Set E) = ⊤) (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ)) :
    ∃ (m : ℤ) (ζ w : E), m ≠ 0 ∧ ξ = (m : ℝ) • ζ ∧ ζ ≠ 0 ∧ ‖ζ‖ ≤ ‖ξ‖ ∧
      (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ζ x = (n : ℝ)) ∧ w ∈ Λ ∧ inner ℝ ζ w = 1 := by
  have hf : normalFunctional ξ ≠ 0 := by
    intro hz
    have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f ξ) hz
    change inner ℝ ξ ξ = 0 at he
    rw [real_inner_self_eq_norm_sq] at he
    have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    nlinarith
  obtain ⟨m, g, w, hm, hfg, hgint, hwΛ, hwg, _⟩ :=
    exists_primitive_lattice_functional Λ (normalFunctional ξ) hspan hint hf
  let ζ := (m : ℝ)⁻¹ • ξ
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hg (x : E) : inner ℝ ζ x = g x := by
    have he := congrArg (fun f : E →ₗ[ℝ] ℝ => f x) hfg
    change inner ℝ ξ x = (m : ℝ) * g x at he
    simp only [ζ, real_inner_smul_left, he]
    field_simp
  have hsplit : ξ = (m : ℝ) • ζ := by
    simp only [ζ, smul_smul, mul_inv_cancel₀ hmR, one_smul]
  refine ⟨m, ζ, w, hm, hsplit, smul_ne_zero (inv_ne_zero hmR) hξ, ?_, ?_, hwΛ, ?_⟩
  · have ha : (1 : ℝ) ≤ |(m : ℝ)| := by
      have hmpos : (0 : ℤ) < |m| := abs_pos.mpr hm
      have hma : (1 : ℤ) ≤ |m| := by omega
      exact_mod_cast hma
    have hnorm : ‖ζ‖ = ‖ξ‖ / |(m : ℝ)| := by
      simp only [ζ, norm_smul, Real.norm_eq_abs, abs_inv, div_eq_mul_inv, mul_comm]
    rw [hnorm]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one ha)).mpr
    exact le_mul_of_one_le_right (norm_nonneg _) ha
  · intro x hx
    rw [hg]
    exact hgint x hx
  · rw [hg]
    exact hwg


/-- Passing to a primitive dual vector decreases both its norm and every
absolute scalar product. The last clause supplies a unit-height lattice vector. -/
theorem exists_primitive_dual_vector (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ξ : E) (hξΛ : ξ ∈ euclideanDualLattice Λ) (hξ : ξ ≠ 0) (y : E) :
    ∃ ζ w : E, ζ ∈ euclideanDualLattice Λ ∧ ζ ≠ 0 ∧ ‖ζ‖ ≤ ‖ξ‖ ∧
      |inner ℝ ζ y| ≤ |inner ℝ ξ y| ∧ w ∈ Λ ∧ inner ℝ ζ w = 1 := by
  obtain ⟨m, ζ, w, hm, he, hζ, hn, hint, hw, hunit⟩ :=
    exists_primitive_lattice_normal Λ (IsZLattice.span_top (K := ℝ)) ξ hξ
      ((mem_euclideanDualLattice Λ ξ).mp hξΛ)
  refine ⟨ζ, w, (mem_euclideanDualLattice Λ ζ).mpr hint, hζ, hn, ?_, hw, hunit⟩
  have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
    have h : (1 : ℤ) ≤ |m| := by have := abs_pos.mpr hm; omega
    exact_mod_cast h
  rw [he, real_inner_smul_left, abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) hm1

end BakerHarman
