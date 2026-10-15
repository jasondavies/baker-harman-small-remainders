import BakerHarman.SharpDimensionInduction
import BakerHarman.DimensionOne
import BakerHarman.HyperplaneBudget
import BakerHarman.Lattice.HyperplaneTransfer

/-!
# Reciprocal approximation by dimension induction

This compatibility interface allows an unspecified logarithmic degree and keeps
`Q ≤ R ^ gammaBH K`. Its proofs specialize `SharpDimensionInduction`, which
supplies degree `d - 1` without a second induction.
-/

namespace BakerHarman

universe u

open OAI.Erdos3

/-- Uniform lattice approximation statement, with explicit constants and
logarithmic degree for use in dimension induction. -/
def ReciprocalLatticeStatement (d : ℕ) (K : ℝ) (m : ℕ) (A B Q₀ R₀ : ℝ) : Prop :=
  ∀ (R : ℝ), R₀ ≤ R → ∀ (Q : ℝ), Q₀ ≤ Q → Q ≤ R ^ gammaBH K →
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E],
  Module.finrank ℝ E = d → ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
  ∀ ρ : ℝ, 1 ≤ ρ → (∀ x ∈ Λ, x ≠ 0 → ρ ≤ ‖x‖) → ZLattice.covolume Λ ≤ Q →
  ∀ y : E, A * R * Q * (Real.log Q + 1) ^ (m + 1) ≤ ‖y‖ → ‖y‖ ≤ R ^ (K + 1) →
    ∃ r : ℤ, R ≤ r ∧ (r : ℝ) ≤ B * R * Q * (Real.log Q + 1) ^ m / ρ ∧
      ∃ v : Λ, ‖(r : ℝ)⁻¹ • y - (v : E)‖ < 1

theorem reciprocalLatticeStatement_one (K : ℝ) (hK : 1 ≤ K) :
    ∃ A B Q₀ R₀ : ℝ, 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ReciprocalLatticeStatement.{u} 1 K 0 A B Q₀ R₀ := by
  exact powerLatticeStatement_one.{u} K hK (gammaBH K)
    (gammaBH_lt_analyticPowerRange K).le

set_option linter.unusedVariables false in
/-- Compatibility form of the successor step at the original power exponent.
The sharp theorem supplies the conclusion directly; the former induction inputs
remain in the signature for existing callers. -/
theorem reciprocalLatticeStatement_succ (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 1 ≤ K)
    (m : ℕ) (A B Q₀ R₀ : ℝ) (hA : 0 < A) (hB : 0 < B) (hQ₀ : 1 ≤ Q₀) (_hR₀ : 2 ≤ R₀)
    (ih : ReciprocalLatticeStatement.{u} d K m A B Q₀ R₀) :
    ∃ (m' : ℕ) (A' B' Q₀' R₀' : ℝ), 0 < A' ∧ 0 < B' ∧ 1 ≤ Q₀' ∧ 2 ≤ R₀' ∧
      ReciprocalLatticeStatement.{u} (d + 1) K m' A' B' Q₀' R₀' := by
  obtain ⟨A', B', Q₀', R₀', hA', hB', hQ₀', hR₀', h⟩ :=
    bakerHarman_sharp_lattice_approximation.{u} (d + 1) (by omega) K hK (gammaBH K)
      (gammaBH_pos K) (gammaBH_lt_analyticPowerRange K)
  exact ⟨(d + 1) - 1, A', B', Q₀', R₀', hA', hB', hQ₀', hR₀', h⟩

/-- Reciprocal approximation for large vectors in every positive dimension.
The logarithmic degree and constants depend only on `d` and `K`. -/
theorem bakerHarman_lattice_approximation (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 1 ≤ K) :
    ∃ (m : ℕ) (A B Q₀ R₀ : ℝ), 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ReciprocalLatticeStatement.{u} d K m A B Q₀ R₀ := by
  obtain ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩ :=
    bakerHarman_sharp_lattice_approximation.{u} d hd K hK (gammaBH K)
      (gammaBH_pos K) (gammaBH_lt_analyticPowerRange K)
  exact ⟨d - 1, A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩

end BakerHarman
