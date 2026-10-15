import BakerHarman.Defs

/-!
# Weighted simultaneous approximation

A rectangular fractional-part partition gives separate coordinate errors, with
a denominator bounded by the product of the integer box sizes.
-/

open scoped BigOperators

namespace BakerHarman

/-- Simultaneous approximation with denominator at most `∏ i, M i` and
coordinate error strictly less than `1 / M i`. -/
theorem weighted_simultaneous_dirichlet {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ι → ℕ) (hM : ∀ i, 0 < M i) :
    ∃ l : ℕ, 0 < l ∧ l ≤ ∏ i, M i ∧
      ∃ p : ι → ℤ, ∀ i, |(l : ℝ) * x i - (p i : ℝ)| < 1 / M i := by
  classical
  have hM0 (i : ι) : (0 : ℝ) < M i := by exact_mod_cast hM i
  let f : Fin ((∏ i, M i) + 1) → (i : ι) → Fin (M i) := fun k i =>
    ⟨⌊(M i : ℝ) * Int.fract ((k : ℕ) * x i)⌋₊,
      (Nat.floor_lt (mul_nonneg (hM0 i).le (Int.fract_nonneg _))).mpr
        (by nlinarith [hM0 i, Int.fract_lt_one ((k : ℕ) * x i)])⟩
  have hcard : Fintype.card ((i : ι) → Fin (M i)) < Fintype.card (Fin ((∏ i, M i) + 1)) := by simp
  have hn := Fintype.not_injective_of_card_lt f hcard
  simp only [Function.Injective] at hn
  push Not at hn
  obtain ⟨u, v, huv, he⟩ : ∃ u v : Fin ((∏ i, M i) + 1), u < v ∧ f u = f v := by
    obtain ⟨u, v, he, hne⟩ := hn
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨u, v, h, he⟩
    · exact ⟨v, u, h, he.symm⟩
  have huvNat : (u : ℕ) < v := huv
  refine ⟨(v : ℕ) - u, Nat.sub_pos_of_lt huvNat, by omega,
    fun i => ⌊(v : ℕ) * x i⌋ - ⌊(u : ℕ) * x i⌋, ?_⟩
  intro i
  have hf : ⌊(M i : ℝ) * Int.fract ((u : ℕ) * x i)⌋₊ =
      ⌊(M i : ℝ) * Int.fract ((v : ℕ) * x i)⌋₊ := congrArg Fin.val (congrFun he i)
  have hlu := Nat.floor_le (mul_nonneg (hM0 i).le (Int.fract_nonneg ((u : ℕ) * x i)))
  have hlv := Nat.floor_le (mul_nonneg (hM0 i).le (Int.fract_nonneg ((v : ℕ) * x i)))
  have hhu := Nat.lt_floor_add_one ((M i : ℝ) * Int.fract ((u : ℕ) * x i))
  have hhv := Nat.lt_floor_add_one ((M i : ℝ) * Int.fract ((v : ℕ) * x i))
  rw [hf] at hlu hhu
  have hbox : |(M i : ℝ) * (Int.fract ((v : ℕ) * x i) - Int.fract ((u : ℕ) * x i))| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith only [hlu, hlv, hhu, hhv]
  rw [abs_mul, abs_of_pos (hM0 i)] at hbox
  have hfrac : |Int.fract ((v : ℕ) * x i) - Int.fract ((u : ℕ) * x i)| < 1 / M i :=
    (lt_div_iff₀ (hM0 i)).mpr (by nlinarith only [hbox])
  convert hfrac using 1
  congr 1
  rw [Nat.cast_sub huvNat.le, Int.cast_sub]
  simp only [Int.fract]
  ring

end BakerHarman
