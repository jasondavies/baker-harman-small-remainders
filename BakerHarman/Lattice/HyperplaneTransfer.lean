import BakerHarman.Lattice.Scaling

/-!
# Lifting reciprocal approximations from a hyperplane

A factor of at least two in the hyperplane lattice leaves half the error budget
for its normal component. This is the geometric step of dimension induction.
-/

namespace BakerHarman

open OAI.Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A lower-dimensional approximation lifts whenever the normal error uses at
most half the unit-radius budget. No integrality of the normal is needed here. -/
theorem reciprocal_latticeHyperplane_transfer (Λ : Submodule ℤ E)
    (ξ y : E) (hξ : ξ ≠ 0) (c : ℝ) (hc : 2 ≤ c) (r : ℝ) (hr : 0 < r)
    (herror : |inner ℝ ξ y| / ‖ξ‖ ≤ r / 2)
    (happrox : ∃ m : scaledLattice (latticeHyperplane Λ (normalFunctional ξ)) c
        (by linarith : c ≠ 0),
      ‖r⁻¹ • (c • (normalFunctional ξ).ker.orthogonalProjectionOnto y) -
        (m : (normalFunctional ξ).ker)‖ < 1) :
    ∃ m : Λ, ‖r⁻¹ • y - (m : E)‖ < 1 := by
  have hc0 : 0 < c := by linarith
  obtain ⟨m, hm⟩ := scaledLattice_reciprocal_approximation
    (latticeHyperplane Λ (normalFunctional ξ)) c hc0 r
    ((normalFunctional ξ).ker.orthogonalProjectionOnto y) happrox
  have hmΛ : ((m : (normalFunctional ξ).ker) : E) ∈ Λ := m.property
  refine ⟨⟨_, hmΛ⟩, ?_⟩
  have hhalf : c⁻¹ ≤ (1 / 2 : ℝ) := by
    exact inv_le_of_inv_le₀ (by norm_num : (0 : ℝ) < 1 / 2) (by simpa using hc)
  have hm' : ‖r⁻¹ • (normalFunctional ξ).ker.starProjection y -
      ((m : (normalFunctional ξ).ker) : E)‖ < 1 / 2 :=
    hm.trans_le hhalf
  have h := reciprocal_normalHyperplane_transfer ξ y ((m : (normalFunctional ξ).ker) : E)
    hξ r (1 / 2) (1 / 2) hr hm' (by simpa only [div_eq_mul_inv, one_mul] using herror)
  norm_num at h ⊢
  exact h

variable [MeasurableSpace E] [BorelSpace E]

/-- The covolume change under the scaled hyperplane step. -/
theorem scaled_latticeHyperplane_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) (c : ℝ) (hc : 0 < c) :
    ZLattice.covolume (scaledLattice (latticeHyperplane Λ (normalFunctional ξ)) c hc.ne') =
      c ^ (Module.finrank ℝ E - 1) * ‖ξ‖ * ZLattice.covolume Λ := by
  let := latticeHyperplane_isZLattice Λ (normalFunctional ξ) hint w hwΛ hw
  have hd : Module.finrank ℝ (normalFunctional ξ).ker = Module.finrank ℝ E - 1 := by
    have := normalHyperplane_finrank ξ hξ
    omega
  rw [scaledLattice_covolume _ c hc, hd, latticeHyperplane_covolume Λ ξ hξ hint w hwΛ hw]
  ring

end BakerHarman
