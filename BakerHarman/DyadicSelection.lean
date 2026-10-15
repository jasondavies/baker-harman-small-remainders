import BakerHarman.LargeSums

/-!
# Selecting reciprocal sums of comparable size

These finite counting lemmas implement the removal of small sums and the dyadic
selection in Baker–Harman, Proposition 3. They are independent of the lattice
Fourier detection theorem supplying the initial lower bound.
-/

namespace BakerHarman

open scoped BigOperators

/-- Discarding terms below `τ` loses at most the number of terms times `τ`. -/
theorem sum_large_terms_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ) (τ : ℝ)
    (hτ : 0 ≤ τ) :
    (∑ i ∈ s, f i) - s.card * τ ≤ ∑ i ∈ s with τ ≤ f i, f i := by
  classical
  have hsmall : (∑ i ∈ s with ¬τ ≤ f i, f i) ≤ s.card * τ := by
    calc
      _ ≤ ∑ i ∈ s with ¬τ ≤ f i, τ := Finset.sum_le_sum fun i hi =>
        (not_le.mp (Finset.mem_filter.mp hi).2).le
      _ = ((s.filter fun i => ¬τ ≤ f i).card : ℝ) * τ := by simp
      _ ≤ s.card * τ := mul_le_mul_of_nonneg_right
        (by exact_mod_cast Finset.card_filter_le s (fun i => ¬τ ≤ f i)) hτ
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => τ ≤ f i) f
  linarith

/-- A finite dyadic partition contains a class whose size times its lower
endpoint is at least the total mass divided by twice the number of classes. -/
theorem exists_dyadic_class {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (b : ℝ) (m : ℕ) (hb : 0 < b) (hm : 0 < m)
    (hlo : ∀ i ∈ s, b ≤ f i) (hhi : ∀ i ∈ s, f i < b * 2 ^ m) :
    ∃ j < m, (∑ i ∈ s, f i) ≤
      2 * m * (b * 2 ^ j) * (s.filter fun i => b * 2 ^ j ≤ f i ∧ f i < b * 2 ^ (j + 1)).card := by
  classical
  let band (j : ℕ) := s.filter fun i => b * 2 ^ j ≤ f i ∧ f i < b * 2 ^ (j + 1)
  have hcover (i : ι) (hi : i ∈ s) : ∃ j ∈ Finset.range m, i ∈ band j := by
    obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near
      ((le_div_iff₀ hb).mpr (by simpa using hlo i hi)) (by norm_num : (1 : ℝ) < 2)
    have hjlower : b * 2 ^ j ≤ f i := by nlinarith [(le_div_iff₀ hb).mp hjlo]
    have hjupper : f i < b * 2 ^ (j + 1) := by nlinarith [(div_lt_iff₀ hb).mp hjhi]
    have hjm : j < m := by
      by_contra h
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (not_lt.mp h)
      have := mul_le_mul_of_nonneg_left hp hb.le
      linarith [hhi i hi]
    exact ⟨j, Finset.mem_range.mpr hjm, Finset.mem_filter.mpr ⟨hi, hjlower, hjupper⟩⟩
  have htotal : (∑ i ∈ s, f i) ≤ ∑ j ∈ Finset.range m, ∑ i ∈ band j, f i := by
    simp only [band, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨j, hj, hij⟩ := hcover i hi
    have hij' := (Finset.mem_filter.mp hij).2
    calc
      f i = (if b * 2 ^ j ≤ f i ∧ f i < b * 2 ^ (j + 1) then f i else 0) := by rw [ite_eq_left hij']
      _ ≤ ∑ k ∈ Finset.range m, if b * 2 ^ k ≤ f i ∧ f i < b * 2 ^ (k + 1) then f i else 0 :=
        Finset.single_le_sum
          (f := fun k => if b * 2 ^ k ≤ f i ∧ f i < b * 2 ^ (k + 1) then f i else 0)
          (fun k _ => by split_ifs <;> linarith [hlo i hi]) hj
  have hband (j : ℕ) : (∑ i ∈ band j, f i) ≤ 2 * (b * 2 ^ j) * (band j).card := by
    calc
      _ ≤ ∑ i ∈ band j, b * 2 ^ (j + 1) := Finset.sum_le_sum fun i hi =>
        (Finset.mem_filter.mp hi).2.2.le
      _ = _ := by simp [pow_succ]; ring
  have htotal' := htotal.trans (Finset.sum_le_sum fun j _ => hband j)
  by_contra h
  push Not at h
  have hsum : (∑ j ∈ Finset.range m, 2 * (b * 2 ^ j) * (band j).card) * m <
      (∑ i ∈ s, f i) * m := by
    rw [Finset.sum_mul]
    calc
      _ < ∑ _j ∈ Finset.range m, ∑ i ∈ s, f i := by
        apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega))
        intro j hj
        have := h j (Finset.mem_range.mp hj)
        dsimp [band] at *
        nlinarith only [this]
      _ = _ := by simp; ring
  have := mul_le_mul_of_nonneg_right htotal' (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  linarith

/-- Two of at least two real values in `[-M,M]` differ by at most `4M/card`.
The indices need not have distinct values: equal values already give a pair. -/
theorem exists_close_pair {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hs : 2 ≤ s.card) (hf : ∀ i ∈ s, |f i| ≤ M) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ |f i - f j| ≤ 4 * M / s.card := by
  classical
  obtain ⟨i₀, hi₀, j₀, hj₀, hne₀⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  have hdiff : |f i₀ - f j₀| ≤ 2 * M := by
    exact (abs_sub _ _).trans (by linarith [hf i₀ hi₀, hf j₀ hj₀])
  by_cases hM0 : M = 0
  · refine ⟨i₀, hi₀, j₀, hj₀, hne₀, ?_⟩
    simpa [hM0] using hdiff
  have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  by_cases hs2 : s.card = 2
  · refine ⟨i₀, hi₀, j₀, hj₀, hne₀, ?_⟩
    rw [hs2]
    norm_num
    linarith
  have hs3 : (2 : ℝ) < s.card := by exact_mod_cast (show 2 < s.card by omega)
  have hcard : (0 : ℝ) < s.card := by linarith
  let D : ℝ := 4 * M / s.card
  have hD : 0 < D := by dsimp [D]; positivity
  let g : ι → ℕ := fun i => ⌊(f i + M) / D⌋₊
  let bins := Finset.range (⌊2 * M / D⌋₊ + 1)
  have hratio : 2 * M / D = (s.card : ℝ) / 2 := by
    dsimp [D]
    field_simp
    norm_num
  have hbin : bins.card < s.card := by
    have hn : (⌊2 * M / D⌋₊ : ℝ) ≤ 2 * M / D := Nat.floor_le (by positivity)
    have hc : (bins.card : ℝ) = (⌊2 * M / D⌋₊ : ℝ) + 1 := by simp [bins]
    have hr : (bins.card : ℝ) < s.card := by rw [hratio] at hn hc; linarith
    exact_mod_cast hr
  have hmap : ∀ i ∈ s, g i ∈ bins := by
    intro i hi
    have hupper := (abs_le.mp (hf i hi)).2
    have hfl : g i ≤ ⌊2 * M / D⌋₊ := Nat.floor_mono
      (div_le_div_of_nonneg_right (by linarith) hD.le)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨i, hi, j, hj, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hbin hmap
  have hnonneg (i : ι) (hi : i ∈ s) : 0 ≤ (f i + M) / D :=
    div_nonneg (by linarith [(abs_le.mp (hf i hi)).1]) hD.le
  have hil := Nat.floor_le (hnonneg i hi)
  have hjl := Nat.floor_le (hnonneg j hj)
  have hiu := Nat.lt_floor_add_one ((f i + M) / D)
  have hju := Nat.lt_floor_add_one ((f j + M) / D)
  change (g i : ℝ) ≤ _ at hil
  change (g j : ℝ) ≤ _ at hjl
  change _ < (g i : ℝ) + 1 at hiu
  change _ < (g j : ℝ) + 1 at hju
  rw [heq] at hil hiu
  have hlowi := (le_div_iff₀ hD).mp hil
  have hlowj := (le_div_iff₀ hD).mp hjl
  have hupi := (div_lt_iff₀ hD).mp hiu
  have hupj := (div_lt_iff₀ hD).mp hju
  exact ⟨i, hi, j, hj, hne, abs_le.mpr ⟨by dsimp [D] at *; nlinarith,
    by dsimp [D] at *; nlinarith⟩⟩

/-- Including the zero value in the box argument permits singleton families:
either one value is small, or two values have a small difference. -/
theorem exists_small_value_or_close_pair {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hs : s.Nonempty) (hf : ∀ i ∈ s, |f i| ≤ M) :
    (∃ i ∈ s, |f i| ≤ 4 * M / s.card) ∨
      ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ |f i - f j| ≤ 4 * M / s.card := by
  by_cases hcard : 2 ≤ s.card
  · exact Or.inr (exists_close_pair s f M hM hcard hf)
  · have hcard1 : s.card = 1 := by have := Finset.card_pos.mpr hs; omega
    obtain ⟨i, hi⟩ := hs
    refine Or.inl ⟨i, hi, ?_⟩
    rw [hcard1]
    norm_num
    linarith [hf i hi]

/-- Dyadic selection followed by the box argument. If weights have total mass
at least `A` and each value is bounded by `C/weight`, there is a value or a
difference of values of size at most `8Cm/A`. This also handles a class
containing just one index. -/
theorem dyadic_small_value_or_difference {ι : Type*} (s : Finset ι)
    (w z : ι → ℝ) (b A C : ℝ) (m : ℕ)
    (hb : 0 < b) (hA : 0 < A) (hC : 0 ≤ C) (hm : 0 < m)
    (hlo : ∀ i ∈ s, b ≤ w i) (hhi : ∀ i ∈ s, w i < b * 2 ^ m)
    (hmass : A ≤ ∑ i ∈ s, w i) (hz : ∀ i ∈ s, |z i| ≤ C / w i) :
    (∃ i ∈ s, |z i| ≤ 8 * C * m / A) ∨
      ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ |z i - z j| ≤ 8 * C * m / A := by
  classical
  obtain ⟨j, _, hclass⟩ := exists_dyadic_class s w b m hb hm hlo hhi
  let B := b * (2 : ℝ) ^ j
  let t := s.filter fun i => B ≤ w i ∧ w i < b * 2 ^ (j + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hprod : A ≤ 2 * m * B * t.card := hmass.trans hclass
  have htcard : (0 : ℝ) < t.card := by
    by_contra h
    have ht0 : t.card = 0 := by exact_mod_cast (le_antisymm (not_lt.mp h) (Nat.cast_nonneg _))
    rw [ht0] at hprod
    norm_num at hprod
    linarith
  have ht : t.Nonempty := Finset.card_pos.mp (by exact_mod_cast htcard)
  have hsub : t ⊆ s := Finset.filter_subset _ _
  have hzt (i : ι) (hi : i ∈ t) : |z i| ≤ C / B := by
    have hwi : B ≤ w i := (Finset.mem_filter.mp hi).2.1
    exact (hz i (hsub hi)).trans (div_le_div_of_nonneg_left hC hB hwi)
  have hbudget : 4 * (C / B) / t.card ≤ 8 * C * m / A := by
    calc
      _ = (4 * C) / (B * t.card) := by field_simp
      _ ≤ _ := by
        rw [div_le_div_iff₀ (mul_pos hB htcard) hA]
        nlinarith only [mul_le_mul_of_nonneg_left hprod hC]
  rcases exists_small_value_or_close_pair t z (C / B) (div_nonneg hC hB.le) ht hzt with h | h
  · obtain ⟨i, hi, hiz⟩ := h
    exact Or.inl ⟨i, hsub hi, hiz.trans hbudget⟩
  · obtain ⟨i, hi, k, hk, hik, hiz⟩ := h
    exact Or.inr ⟨i, hsub hi, k, hsub hk, hik, hiz.trans hbudget⟩

/-- The ratio between the trivial bound `2R` and the cutoff `RQ^(-11/10)`
requires only logarithmically many dyadic classes. -/
theorem exists_dyadic_length (Q : ℝ) (hQ : 1 ≤ Q) :
    ∃ m : ℕ, 0 < m ∧ 2 * Q ^ (11 / 10 : ℝ) < (2 : ℝ) ^ m ∧
      (m : ℝ) ≤ (2 + (11 / 10 : ℝ) / Real.log 2) * (Real.log Q + 1) := by
  have hQ0 : 0 < Q := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  let x : ℝ := 1 + (11 / 10 : ℝ) * Real.log Q / Real.log 2
  let m : ℕ := ⌊x⌋₊ + 1
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hmlo : x < (m : ℝ) := by simpa [m] using Nat.lt_floor_add_one x
  have hmhi : (m : ℝ) ≤ x + 1 := by
    have := Nat.floor_le hx0
    dsimp [m]
    push_cast
    linarith
  refine ⟨m, by dsimp [m]; omega, ?_, ?_⟩
  · have hx : Real.logb 2 (2 * Q ^ (11 / 10 : ℝ)) = x := by
      rw [Real.logb, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hQ0 _).ne',
        Real.log_rpow hQ0]
      dsimp [x]
      field_simp
    have hp := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2)
      (by positivity : 0 < 2 * Q ^ (11 / 10 : ℝ))).mp (hx ▸ hmlo)
    simpa only [Real.rpow_natCast] using hp
  · have hc : 0 ≤ (11 / 10 : ℝ) / Real.log 2 := by positivity
    dsimp [x] at hmhi
    have he : (11 / 10 : ℝ) * Real.log Q / Real.log 2 =
        ((11 / 10 : ℝ) / Real.log 2) * Real.log Q := by ring
    rw [he] at hmhi
    nlinarith

/-- When there are at most `DQ(log Q+1)^n` frequencies, discarding sums below
`RQ^(-11/10)` preserves half of any lower bound `cR`, once `Q` is large.
The threshold is uniform in the finite family and in `R`. -/
theorem large_terms_retain_mass_log_factor (D c : ℝ) (n : ℕ) (hc : 0 < c) :
    ∀ᶠ Q : ℝ in Filter.atTop, ∀ (ι : Type*) (s : Finset ι) (w : ι → ℝ) (R : ℝ),
      0 ≤ R → (s.card : ℝ) ≤ D * (Real.log Q + 1) ^ n * Q → c * R ≤ ∑ i ∈ s, w i →
      c * R / 2 ≤ ∑ i ∈ s with R * Q ^ (-(11 / 10 : ℝ)) ≤ w i, w i := by
  have hgrow := log_add_one_pow_absorbed (2 * D / c) (1 / 10 : ℝ) n (by norm_num)
  filter_upwards [hgrow, Filter.eventually_ge_atTop (1 : ℝ)] with Q hgrow hQ
  intro ι s w R hR hcard hmass
  have hQ0 : 0 < Q := by linarith
  have hpow : 0 < Q ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hQ0 _
  have hscale : (D * (Real.log Q + 1) ^ n) * Q ^ (-(1 / 10 : ℝ)) ≤ c / 2 := by
    rw [Real.rpow_neg hQ0.le, ← div_eq_mul_inv]
    apply (div_le_iff₀ hpow).mpr
    rw [div_mul_eq_mul_div] at hgrow
    have := (div_le_iff₀ hc).mp hgrow
    nlinarith
  have hid : Q * Q ^ (-(11 / 10 : ℝ)) = Q ^ (-(1 / 10 : ℝ)) := by
    conv_lhs => lhs; rw [← Real.rpow_one Q]
    rw [← Real.rpow_add hQ0]
    norm_num
  have hsmall : (s.card : ℝ) * (R * Q ^ (-(11 / 10 : ℝ))) ≤ c * R / 2 := by
    calc
      _ ≤ (D * (Real.log Q + 1) ^ n * Q) * (R * Q ^ (-(11 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = R * ((D * (Real.log Q + 1) ^ n) * Q ^ (-(1 / 10 : ℝ))) := by rw [← hid]; ring
      _ ≤ R * (c / 2) := mul_le_mul_of_nonneg_left hscale hR
      _ = _ := by ring
  have h := sum_large_terms_ge s w (R * Q ^ (-(11 / 10 : ℝ))) (by positivity)
  linarith

/-- Fixed-factor frequency-count version of the small-sum removal lemma. -/
theorem large_terms_retain_mass (D c : ℝ) (hc : 0 < c) :
    ∀ᶠ Q : ℝ in Filter.atTop, ∀ (ι : Type*) (s : Finset ι) (w : ι → ℝ) (R : ℝ),
      0 ≤ R → (s.card : ℝ) ≤ D * Q → c * R ≤ ∑ i ∈ s, w i →
      c * R / 2 ≤ ∑ i ∈ s with R * Q ^ (-(11 / 10 : ℝ)) ≤ w i, w i := by
  simpa only [pow_zero, mul_one] using large_terms_retain_mass_log_factor D c 0 hc

end BakerHarman
