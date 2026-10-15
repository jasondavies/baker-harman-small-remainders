import BakerHarmanAnalytics.LatticeHyperplaneBasis

/-!
# Euclidean dual lattices

Adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Combinatorics/Progressions/Lattices/NormalizedLatticeSheet.lean`.
These declarations are extracted into the project namespace to avoid unrelated
imports. Upstream code is licensed under Apache 2.0; see
`vendor/baker-harman-analytics/LICENSE`.
-/

namespace BakerHarman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanDualLattice (Λ : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) Λ

theorem mem_euclideanDualLattice (Λ : Submodule ℤ E) (ξ : E) :
    ξ ∈ euclideanDualLattice Λ ↔ ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ) := by
  simp only [euclideanDualLattice, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, innerₗ_apply_apply]
  exact forall_congr' (fun _ => forall_congr' (fun _ => exists_congr (fun _ => eq_comm)))

theorem realInner_nondegenerate : (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

variable [FiniteDimensional ℝ E]

theorem euclideanDualLattice_eq_span_dualBasis (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] :
    euclideanDualLattice Λ = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (innerₗ E) realInner_nondegenerate
        ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ))) := by
  have h := LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (innerₗ E) realInner_nondegenerate
    ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, Module.Basis.ofZLatticeBasis_span] using h

instance euclideanDualLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : DiscreteTopology (euclideanDualLattice Λ) := by
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  infer_instance

instance euclideanDualLattice_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : IsZLattice ℝ (euclideanDualLattice Λ) := by
  constructor
  rw [euclideanDualLattice_eq_span_dualBasis Λ]
  exact IsZLattice.span_top (K := ℝ)

theorem euclideanDualLattice_involutive (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : euclideanDualLattice (euclideanDualLattice Λ) = Λ := by
  have hsymm : LinearMap.BilinForm.IsSymm (innerₗ E) := ⟨fun _ _ => real_inner_comm _ _⟩
  have h := LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis (R := ℤ) (innerₗ E)
    realInner_nondegenerate hsymm ((Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ)
  simpa only [euclideanDualLattice, Module.Basis.ofZLatticeBasis_span] using h


end BakerHarman
