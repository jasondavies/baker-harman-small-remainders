import BakerHarman.ReciprocalSum
import BakerHarmanAnalytics.CorrelationPhase
import BakerHarmanAnalytics.ReciprocalPhaseRegularity

/-!
# Differencing reciprocal phases

The derivative scale keeps the total derivative order fixed while a difference
adds one shift and removes one derivative. Its exact multiplication by the shift
is what permits an optimized van der Corput induction.
-/

open scoped BigOperators
open OAI.Problem337

namespace BakerHarman

/-- Lower derivative scale on `[R,3R]` at fixed total order `D`. -/
noncomputable def reciprocalDerivativeScale (D : ℕ) (hs : List ℝ) (Z R : ℝ) : ℝ :=
  hs.prod * (D.factorial : ℝ) * |Z| / (3 * R) ^ (D + 1)

lemma reciprocalDerivativeScale_pos (D : ℕ) (hs : List ℝ) (Z R : ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) (hZ : Z ≠ 0) (hR : 0 < R) :
    0 < reciprocalDerivativeScale D hs Z R := by
  have hp : 0 < hs.prod := List.prod_pos hhs
  have hz : 0 < |Z| := abs_pos.mpr hZ
  unfold reciprocalDerivativeScale
  positivity

lemma reciprocalDerivativeScale_cons (D : ℕ) (hs : List ℝ) (h Z R : ℝ) :
    reciprocalDerivativeScale D (h :: hs) Z R = h * reciprocalDerivativeScale D hs Z R := by
  simp only [reciprocalDerivativeScale, List.prod_cons]
  ring

/-- All derivatives used during differencing have the same comparison constant
when the sum of the derivative order and the number of shifts stays fixed. -/
theorem reciprocal_differenced_derivative_bounds (D k : ℕ) (hs : List ℝ)
    (Z R x : ℝ) (horder : hs.length + k = D)
    (hhs : ∀ h ∈ hs, 0 < h) (hR : 0 < R)
    (hx : R ≤ x) (hend : x + hs.sum ≤ 3 * R) :
    reciprocalDerivativeScale D hs Z R ≤
        |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ∧
      |iteratedDeriv k (forwardDifference hs (fun y => Z / y)) x| ≤
        (3 : ℝ) ^ (D + 1) * reciprocalDerivativeScale D hs Z R := by
  have h := reciprocal_forwardDifference_derivative_bounds_interval k hs hhs Z hR hx hend
  rw [horder] at h
  have heq : (3 : ℝ) ^ (D + 1) * reciprocalDerivativeScale D hs Z R =
      hs.prod * (D.factorial : ℝ) * |Z| / R ^ (D + 1) := by
    unfold reciprocalDerivativeScale
    rw [mul_pow]
    field_simp
  rw [heq]
  exact h

/-- The terminal second-derivative test for every positively differenced
reciprocal phase. It retains the full derivative-scale dependence. -/
theorem reciprocal_differenced_second_derivative (D : ℕ) (hs : List ℝ)
    (Z R x : ℝ) (N : ℕ) (horder : hs.length + 2 = D)
    (hhs : ∀ h ∈ hs, 0 < h) (hZ : Z ≠ 0) (hR : 0 < R)
    (hx : R ≤ x) (hend : x + N + hs.sum ≤ 3 * R) :
    ‖∑ j ∈ Finset.range N, differencingPhase (forwardDifference hs (fun y => Z / y)
      ((j : ℝ) + x))‖ ≤
      (6 * (3 : ℝ) ^ (D + 1) + 15) *
        ((N : ℝ) * Real.sqrt (reciprocalDerivativeScale D hs Z R) +
          1 / Real.sqrt (reciprocalDerivativeScale D hs Z R)) := by
  have hnonneg : ∀ h ∈ hs, 0 ≤ h := fun h hh => (hhs h hh).le
  have hdata (y : ℝ) (hy : y ∈ Set.Icc x (x + N)) :=
    reciprocal_forwardDifference_second_derivative_data hs hnonneg Z
      (hR.trans_le (hx.trans hy.1))
  apply ExponentialSum.second_derivative_test
    (forwardDifference hs (fun y => Z / y))
    (iteratedDeriv 1 (forwardDifference hs (fun y => Z / y)))
    (iteratedDeriv 2 (forwardDifference hs (fun y => Z / y))) x N
    (reciprocalDerivativeScale D hs Z R) ((3 : ℝ) ^ (D + 1))
    (reciprocalDerivativeScale_pos D hs Z R hhs hZ hR) (by positivity)
    (fun y hy => (hdata y hy).1) (fun y hy => (hdata y hy).2)
  intro y hy
  exact reciprocal_differenced_derivative_bounds D 2 hs Z R y horder hhs hR
    (hx.trans hy.1) (by linarith [hy.2])

end BakerHarman
