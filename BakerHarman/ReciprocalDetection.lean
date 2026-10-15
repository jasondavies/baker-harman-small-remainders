import BakerHarman.Lattice.DetectionBudget
import BakerHarman.DyadicSelection

/-!
# Matching reciprocal sums to lattice detection

The interval `[ceil R, floor (2R)]` has length comparable to `R` even when `R`
is real. On this interval, the lattice characters of `r⁻¹ y` are exactly the
scalar reciprocal phases used by the analytic estimates.
-/

namespace BakerHarman

open OAI.Problem337

/-- Integer interval for reciprocal sums, with uniform bounds on its cardinality. -/
theorem exists_reciprocal_interval (R : ℝ) (hR : 2 ≤ R) :
    ∃ L U : ℤ, R ≤ L ∧ (U : ℝ) ≤ 2 * R ∧
      R / 2 ≤ ((Finset.Icc L U).card : ℝ) ∧ ((Finset.Icc L U).card : ℝ) ≤ 2 * R := by
  let L : ℤ := ⌈R⌉
  let U : ℤ := ⌊2 * R⌋
  have hLlo : R ≤ (L : ℝ) := Int.le_ceil R
  have hLhi : (L : ℝ) < R + 1 := Int.ceil_lt_add_one R
  have hUlo : 2 * R - 1 < (U : ℝ) := Int.sub_one_lt_floor (2 * R)
  have hUhi : (U : ℝ) ≤ 2 * R := Int.floor_le (2 * R)
  have hLU : L ≤ U := by exact_mod_cast (show (L : ℝ) ≤ U by linarith)
  have hcard : ((Finset.Icc L U).card : ℝ) = (U : ℝ) + 1 - L := by
    exact_mod_cast (Int.card_Icc_of_le L U (by omega))
  exact ⟨L, U, hLlo, hUhi, by rw [hcard]; linarith, by rw [hcard]; linarith⟩

/-- The phase used by Poisson summation matches the scalar analytic phase. -/
theorem euclideanCharacter_reciprocal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ξ y : E) (r : ℝ) :
    euclideanCharacter ξ (r⁻¹ • y) = differencingPhase (inner ℝ ξ y / r) := by
  rw [euclideanCharacter_eq_exp, inner_smul_right]
  unfold differencingPhase
  push_cast
  congr 1
  ring

/-- Trivial reciprocal-sum bound used for the upper endpoint of the dyadic
partition. It applies to every real numerator, including zero. -/
theorem reciprocal_sum_le_card (Z : ℝ) (L U : ℤ) :
    ‖∑ r ∈ Finset.Icc L U, differencingPhase (Z / r)‖ ≤ (Finset.Icc L U).card := by
  calc
    _ ≤ ∑ r ∈ Finset.Icc L U, ‖differencingPhase (Z / r)‖ := norm_sum_le _ _
    _ = _ := by simp

end BakerHarman
