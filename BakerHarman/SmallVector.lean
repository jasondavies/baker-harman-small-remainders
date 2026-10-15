import BakerHarman.WeightedSmallVector

/-!
# Small-vector approximation with equal tolerances

Specialize `small_vector_weighted_reciprocal` to a common tolerance and box
size. The simultaneous approximation and rounding argument is proved in
`WeightedSmallVector`.
-/

namespace BakerHarman

/-- Explicit small-vector criterion. The two numerical budgets control the
Dirichlet denominator and the sum of approximation and rounding errors. -/
theorem small_vector_reciprocal {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (R Q ψ : ℝ) (hR : 5 ≤ R) (hQ : 1 ≤ Q) (hψ : 0 < ψ)
    (M : ℕ) (hM : 0 < M)
    (hden : (M : ℝ) ^ (n - 1) ≤ (5 / 4 : ℝ) * Q * ψ)
    (hsmall : ∀ i, a i ≤ R * Q)
    (haccuracy : ∀ i, 1 / (M : ℝ) + a i / R ^ 2 ≤ ψ) :
    ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧ ∀ i, distNearestInt (a i / r) ≤ ψ := by
  apply small_vector_weighted_reciprocal hn a ha R Q (fun _ => ψ) hR hQ
    (fun _ => hψ) (fun _ => M) (fun _ => hM) _ hsmall haccuracy
  intro k
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_subtype_compl,
    Fintype.card_fin, Fintype.card_subtype_eq] using hden

end BakerHarman
