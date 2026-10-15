import BakerHarman.Defs

/-!
# Exponent bookkeeping for Baker–Harman

The original paper's equation (2.1) rounds the derivative order to an integer. Its
Lemma 1 proof actually gives a larger saving before weakening it to `2c(K)`.
We prove that this retained saving exceeds the shifted-sets exponent `gammaBH`,
with room for the small-sum cutoff in Proposition 3.

These are numerical inequalities only. Neither the exponential-sum estimate nor
Baker–Harman's lattice argument is proved in this file.

## How the comparison fits the original proof

Write `M = max 1 K`, `k = ceil(1 + M)`, and `s = (k - M)/(2^k - 2)`.
The exponent pair in Lemma 1 is `(a,b) = (1/(2^k-2), (2^k-k-1)/(2^k-2))`.
Its contribution `|z|^a * R^(b-2a)` is at most `R^(1-s)` for
`|z| ≤ R^(K+1)` and `R ≥ 1`. The paper weakens this saving to `2c(K)`.

For `k ≥ 3`, set `d = k-M ∈ [1,2]` and `A = 2^k ≥ 8`. Bernoulli's
inequality gives `2^(d-1) ≤ d`, so `d * 2^(2-d) ≥ 2`. Consequently
`d * (2^(M+2)-4) ≥ 2A-8 ≥ (4/3)*(A-2)`, proving `s ≥ (4/3)*gammaBH K`.
The remaining case `k = 2` has `M = 1`, `s = 1/2` and `gammaBH K = 1/4`.

In Proposition 3 (pp. 64–65), use cutoff `R * Q^(-5/4)`. The `O(Q)`
small sums then total `O(R * Q^(-1/4))`, negligible for large `Q`. Since
`Q ≤ R^gammaBH`, the cutoff is at least `R^(1-(5/4)*gammaBH)`. The gap
`s - (5/4)*gammaBH ≥ gammaBH/12 > 0` absorbs the power term, leaving the
reciprocal term `R²/|z|` to control large sums as in the original argument.
`bakerHarman_power_term_absorbed` verifies this absorption uniformly in `Q`.

This supplies the numerical margin for adapting the proof. The separate
`BakerHarman.ExponentialSum` module proves the analytic bound using saving
`6 * gammaBH K / 5`. A Gaussian alternative to Fourier detection is proved in
`BakerHarman.Lattice.DetectionBudget`. The lattice induction and final equal-weight
approximation are proved in `BakerHarman.DimensionInduction` and `BakerHarman.EqualWeights`,
which yield the equal-weight small-remainders theorem.
-/

namespace BakerHarman

lemma gammaBH_denom_ge (K : ℝ) : 4 ≤ (2:ℝ) ^ (2 + max 1 K) - 4 := by
  have : (2:ℝ) ^ (3:ℝ) ≤ (2:ℝ) ^ (2 + max 1 K) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [le_max_left 1 K])
  have h8 : (2:ℝ) ^ (3:ℝ) = 8 := by norm_num
  linarith

lemma gammaBH_pos (K : ℝ) : 0 < gammaBH K := by
  unfold gammaBH; have := gammaBH_denom_ge K; positivity

lemma gammaBH_le (K : ℝ) : gammaBH K ≤ 1 / 4 := by
  unfold gammaBH; exact one_div_le_one_div_of_le (by norm_num) (gammaBH_denom_ge K)

lemma gammaBH_antitone : Antitone gammaBH := by
  intro x y hxy
  unfold gammaBH
  apply one_div_le_one_div_of_le (by linarith [gammaBH_denom_ge x])
  have := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num)
    (show 2 + max 1 x ≤ 2 + max 1 y by linarith [max_le_max (le_refl (1:ℝ)) hxy])
  linarith

lemma gammaBH_continuous : Continuous gammaBH := by
  unfold gammaBH
  refine continuous_const.div ?_ (fun K => by have := gammaBH_denom_ge K; intro h; linarith)
  exact (continuous_const.rpow (continuous_const.add (continuous_const.max continuous_id))
    (fun _ => Or.inl (by norm_num))).sub continuous_const

/-- The integer order used in Baker–Harman, equation (2.1). -/
noncomputable def bakerHarmanOrder (K : ℝ) : ℕ := ⌈1 + max 1 K⌉₊

/-- The saving retained from the exponent pair in the proof of Lemma 1, using
`max 1 K` in place of `K` (which only weakens the estimate when `K < 1`). -/
noncomputable def bakerHarmanSaving (K : ℝ) : ℝ :=
  ((bakerHarmanOrder K : ℝ) - max 1 K) / ((2 : ℝ) ^ bakerHarmanOrder K - 2)

lemma bakerHarmanOrder_bounds (K : ℝ) :
    1 + max 1 K ≤ (bakerHarmanOrder K : ℝ) ∧
      (bakerHarmanOrder K : ℝ) < 2 + max 1 K := by
  constructor
  · exact Nat.le_ceil _
  · have := Nat.ceil_lt_add_one (show 0 ≤ 1 + max 1 K by linarith [le_max_left 1 K])
    dsimp [bakerHarmanOrder]
    linarith

/-- Substituting `|z| ≤ R^(K+1)` in `|z|^a * R^(b-2a)`, with the
exponent pair `(a,b)` from Lemma 1, gives an exponent at most `1 - saving`. -/
lemma bakerHarman_exponent_pair_bound (K : ℝ) :
    (K - 1) / ((2 : ℝ) ^ bakerHarmanOrder K - 2) +
        ((2 : ℝ) ^ bakerHarmanOrder K - (bakerHarmanOrder K : ℝ) - 1) /
          ((2 : ℝ) ^ bakerHarmanOrder K - 2) ≤
      1 - bakerHarmanSaving K := by
  have hk : 2 ≤ bakerHarmanOrder K := by
    exact_mod_cast (show (2 : ℝ) ≤ bakerHarmanOrder K by
      linarith [(bakerHarmanOrder_bounds K).1, le_max_left 1 K])
  have hA : (4 : ℝ) ≤ 2 ^ bakerHarmanOrder K := by
    calc
      (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      _ ≤ 2 ^ bakerHarmanOrder K := pow_le_pow_right₀ (by norm_num) hk
  have hden : 0 < (2 : ℝ) ^ bakerHarmanOrder K - 2 := by linarith
  unfold bakerHarmanSaving
  rw [← add_div, le_sub_iff_add_le, ← add_div, div_le_iff₀ hden]
  linarith [le_max_right 1 K]

/-- Keeping the saving in the original exponent-pair estimate leaves a uniform
margin beyond the exponent quoted in the shifted-sets paper. -/
theorem four_thirds_gammaBH_le_bakerHarmanSaving (K : ℝ) :
    (4 / 3 : ℝ) * gammaBH K ≤ bakerHarmanSaving K := by
  obtain ⟨hlo, hhi⟩ := bakerHarmanOrder_bounds K
  have hM : 1 ≤ max 1 K := le_max_left _ _
  have hk2 : 2 ≤ bakerHarmanOrder K := by exact_mod_cast (show (2 : ℝ) ≤ bakerHarmanOrder K by linarith)
  by_cases hk : bakerHarmanOrder K = 2
  · have hm : max 1 K = 1 := by rw [hk] at hlo; norm_num at hlo; linarith
    norm_num [bakerHarmanSaving, gammaBH, hk, hm]
  have hk3 : 3 ≤ bakerHarmanOrder K := by omega
  have hA : (8 : ℝ) ≤ 2 ^ bakerHarmanOrder K := by
    calc
      (8 : ℝ) = 2 ^ (3 : ℕ) := by norm_num
      _ ≤ 2 ^ bakerHarmanOrder K := pow_le_pow_right₀ (by norm_num) hk3
  let d : ℝ := (bakerHarmanOrder K : ℝ) - max 1 K
  have hd1 : 1 ≤ d := by dsimp [d]; linarith
  have hd2 : d ≤ 2 := by dsimp [d]; linarith
  have hchord : (2 : ℝ) ^ (d - 1) ≤ d := by
    have := rpow_one_add_le_one_add_mul_self (s := (1 : ℝ)) (by norm_num)
      (show 0 ≤ d - 1 by linarith) (show d - 1 ≤ 1 by linarith)
    norm_num at this
    linarith
  have hprod : (2 : ℝ) ^ (d - 1) * 2 ^ (2 - d) = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have htwo : 2 ≤ d * (2 : ℝ) ^ (2 - d) := by
    calc
      (2 : ℝ) = 2 ^ (d - 1) * 2 ^ (2 - d) := hprod.symm
      _ ≤ d * 2 ^ (2 - d) :=
        mul_le_mul_of_nonneg_right hchord (Real.rpow_nonneg (by norm_num) _)
  have hscale : (2 : ℝ) ^ (2 + max 1 K) =
      2 ^ bakerHarmanOrder K * (2 : ℝ) ^ (2 - d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    dsimp [d]
    ring
  have hmain : 2 * (2 : ℝ) ^ bakerHarmanOrder K ≤ d * (2 : ℝ) ^ (2 + max 1 K) := by
    rw [hscale]
    nlinarith [mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ 2 ^ bakerHarmanOrder K by positivity)]
  change (4 / 3 : ℝ) * (1 / ((2 : ℝ) ^ (2 + max 1 K) - 4)) ≤
    d / ((2 : ℝ) ^ bakerHarmanOrder K - 2)
  rw [mul_one_div, div_le_div_iff₀ (by linarith [gammaBH_denom_ge K]) (by linarith)]
  nlinarith

/-- With cutoff `R * Q^(-5/4)`, the saving beats the cutoff exponent by at least
`gammaBH K / 12`. This positive margin absorbs fixed constants as `R` grows. -/
theorem bakerHarman_cutoff_gap (K : ℝ) :
    0 < gammaBH K / 12 ∧
      gammaBH K / 12 ≤ bakerHarmanSaving K - (5 / 4 : ℝ) * gammaBH K := by
  constructor
  · exact div_pos (gammaBH_pos K) (by norm_num)
  · linarith [four_thirds_gammaBH_le_bakerHarmanSaving K]

/-- Uniformly for `0 < Q ≤ R^gammaBH`, the power term in the retained
exponential-sum bound is eventually at most half the large-sum cutoff.
The reciprocal term `R² / |z|` must therefore account for any sum exceeding
that cutoff, once an exponential-sum bound has been supplied. -/
theorem bakerHarman_power_term_absorbed (K C : ℝ) :
    ∀ᶠ R : ℝ in Filter.atTop, ∀ Q : ℝ, 0 < Q → Q ≤ R ^ gammaBH K →
      C * R ^ (1 - bakerHarmanSaving K) ≤ R * Q ^ (-(5 / 4 : ℝ)) / 2 := by
  let gap := bakerHarmanSaving K - (5 / 4 : ℝ) * gammaBH K
  have hgap : 0 < gap := lt_of_lt_of_le (bakerHarman_cutoff_gap K).1
    (bakerHarman_cutoff_gap K).2
  have hgrow : ∀ᶠ R : ℝ in Filter.atTop, 2 * C ≤ R ^ gap :=
    (tendsto_rpow_atTop hgap).eventually (Filter.eventually_ge_atTop (2 * C))
  filter_upwards [hgrow, Filter.eventually_ge_atTop (1 : ℝ)] with R hR hR1
  intro Q hQ hQR
  have hR0 : 0 < R := by linarith
  have hcut : R ^ (1 - (5 / 4 : ℝ) * gammaBH K) ≤ R * Q ^ (-(5 / 4 : ℝ)) := by
    calc
      R ^ (1 - (5 / 4 : ℝ) * gammaBH K) =
          R * (R ^ gammaBH K) ^ (-(5 / 4 : ℝ)) := by
        rw [← Real.rpow_mul hR0.le]
        conv_rhs => lhs; rw [← Real.rpow_one R]
        rw [← Real.rpow_add hR0]
        congr 1
        ring
      _ ≤ R * Q ^ (-(5 / 4 : ℝ)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hQ hQR (by norm_num)) hR0.le
  have hmul := mul_le_mul_of_nonneg_right hR
    (Real.rpow_nonneg hR0.le (1 - bakerHarmanSaving K))
  have hid : R ^ gap * R ^ (1 - bakerHarmanSaving K) =
      R ^ (1 - (5 / 4 : ℝ) * gammaBH K) := by
    rw [← Real.rpow_add hR0]
    congr 1
    dsimp [gap]
    ring
  rw [hid] at hmul
  nlinarith

end BakerHarman
