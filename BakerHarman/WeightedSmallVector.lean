import BakerHarman.ReciprocalRounding
import BakerHarman.WeightedDirichlet

/-!
# The small-vector reciprocal approximation step with unequal weights

A coordinate with maximal ratio to its tolerance determines the reciprocal
modulus. The other coordinates are approximated with rectangular Dirichlet boxes
before rounding that modulus to an integer.
-/

namespace BakerHarman

/-- Explicit small-vector criterion. The two numerical budgets control the
Dirichlet denominator and the sum of approximation and rounding errors. -/
theorem small_vector_weighted_reciprocal {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (R Q : ℝ) (ψ : Fin n → ℝ) (hR : 5 ≤ R) (hQ : 1 ≤ Q) (hψ : ∀ i, 0 < ψ i)
    (M : Fin n → ℕ) (hM : ∀ i, 0 < M i)
    (hden : ∀ k, (∏ i : {i : Fin n // i ≠ k}, (M i : ℝ)) ≤ (5 / 4 : ℝ) * Q * ψ k)
    (hsmall : ∀ i, a i ≤ R * Q)
    (haccuracy : ∀ i, 1 / (M i : ℝ) + a i / R ^ 2 ≤ ψ i) :
    ∃ r : ℕ, R ≤ r ∧ (r : ℝ) ≤ 2 * Q * R ∧ ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hR0 : 0 < R := by linarith
  have hQ0 : 0 < Q := by linarith
  have hRQ : 2 ≤ R * Q := by nlinarith [mul_le_mul_of_nonneg_left hQ hR0.le]
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun i => a i / ψ i) Finset.univ_nonempty
  have hmax : ∀ i, a i / ψ i ≤ a k / ψ k := fun i => hk i (Finset.mem_univ i)
  by_cases htriv : a k ≤ (3 / 2 : ℝ) * R * Q * ψ k
  · let r := ⌈(3 / 2 : ℝ) * R * Q⌉₊
    have hrlo : (3 / 2 : ℝ) * R * Q ≤ r := Nat.le_ceil _
    have hrhi : (r : ℝ) < (3 / 2 : ℝ) * R * Q + 1 := Nat.ceil_lt_add_one (by positivity)
    have hrR : R ≤ r := by nlinarith only [hrlo, hQ, hR0, hRQ]
    have hr0 : (0 : ℝ) < r := hR0.trans_le hrR
    refine ⟨r, hrR, by nlinarith only [hrhi, hRQ], ?_⟩
    intro i
    have hile : a i / ψ i ≤ (3 / 2 : ℝ) * R * Q :=
      (hmax i).trans ((div_le_iff₀ (hψ k)).mpr htriv)
    have hile' := (div_le_iff₀ (hψ i)).mp hile
    have hle : a i / r ≤ ψ i := (div_le_iff₀ hr0).mpr (by
      nlinarith only [hile', mul_le_mul_of_nonneg_right hrlo (hψ i).le])
    exact (round_le (a i / r) 0).trans (by
      simpa only [Int.cast_zero, sub_zero, abs_of_nonneg (div_nonneg (ha i) hr0.le)] using hle)
  have hx : 0 < a k := by
    have hpos : 0 < (3 / 2 : ℝ) * R * Q * ψ k := by positivity [hψ k]
    exact hpos.trans (lt_of_not_ge htriv)
  let I := {i : Fin n // i ≠ k}
  obtain ⟨l, hl0, hlM, p, hp⟩ := weighted_simultaneous_dirichlet (fun i : I => a i / a k) (fun i => M i) (fun i => hM i)
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl0
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl0
  have hlupper : (l : ℝ) ≤ (5 / 4 : ℝ) * Q * ψ k := by
    have hh : (l : ℝ) ≤ ∏ i : I, (M i : ℝ) := by exact_mod_cast hlM
    exact hh.trans (hden k)
  have hxlarge : R + 1 ≤ a k / l := by
    apply (le_div_iff₀ hlpos).mpr
    have hRl : (R + 1) * (l : ℝ) ≤ (R + 1) * ((5 / 4 : ℝ) * Q * ψ k) :=
      mul_le_mul_of_nonneg_left hlupper (by positivity)
    have hg : (R + 1) * ((5 / 4 : ℝ) * Q * ψ k) ≤ (3 / 2 : ℝ) * R * Q * ψ k := by
      nlinarith only [mul_nonneg (show 0 ≤ R - 5 by linarith) (mul_nonneg hQ0.le (hψ k).le)]
    exact (hRl.trans hg).trans (le_of_lt (lt_of_not_ge htriv))
  let r := ⌊a k / (l : ℝ)⌋₊
  obtain ⟨hrR, hrx, hlow, hupp⟩ := reciprocal_floor_bounds (a k) l R hx hl1 hR0 hxlarge
  have hr0 : (0 : ℝ) < r := hR0.trans_le hrR
  refine ⟨r, hrR, (hrx.trans (hsmall k)).trans (by nlinarith only [hRQ]), ?_⟩
  intro i
  let z : ℤ := if hi : i = k then (l : ℤ) else p ⟨i, hi⟩
  have happrox : |(l : ℝ) * a i / a k - (z : ℝ)| ≤ 1 / M i := by
    by_cases hi : i = k
    · simp only [z, dite_eq_left hi, hi, Int.cast_natCast]
      rw [mul_div_cancel_right₀ _ hx.ne', sub_self, abs_zero]
      positivity
    · simpa only [z, dite_eq_right hi, mul_div_assoc] using (hp ⟨i, hi⟩).le
  have hround := reciprocal_rounding_error (a i) (a k) l r R (ha i) hx hR0 hrR hlow hupp
  have herr : |a i / r - (z : ℝ)| ≤ ψ i := by
    calc
      _ ≤ |a i / r - (l : ℝ) * a i / a k| + |(l : ℝ) * a i / a k - (z : ℝ)| :=
        abs_sub_le _ _ _
      _ ≤ a i / R ^ 2 + 1 / M i := add_le_add hround happrox
      _ ≤ ψ i := by linarith only [haccuracy i]
  exact (round_le (a i / r) z).trans herr

end BakerHarman
