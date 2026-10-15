import Mathlib

/-!
Adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Combinatorics/Progressions/Estimates/UniformIntegralSeries.lean`.
The imports and namespace are reduced to this proof dependency.
Upstream code is licensed under Apache 2.0; see
`vendor/baker-harman-analytics/LICENSE`.
-/

namespace BakerHarman

section


open MeasureTheory Filter

theorem integral_tsum_of_uniform_domination {ι X V : Type*} [Countable ι]
    [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure X) [IsFiniteMeasure μ] (f : ι → X → V) (C : ι → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hC : Summable C)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C i) :
    (∫ x, ∑' i, f i x ∂μ) = ∑' i, ∫ x, f i x ∂μ := by
  symm
  apply HasSum.tsum_eq
  apply hasSum_integral_of_dominated_convergence (fun i _ => C i) hf hbound
  · exact Eventually.of_forall (fun _ => hC)
  · exact integrable_const _
  · filter_upwards [ae_all_iff.mpr hbound] with x hx
    exact (hC.of_norm_bounded hx).hasSum


end

end BakerHarman
