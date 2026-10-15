import BakerHarman.Defs

/-!
# Simultaneous Dirichlet approximation

Partition the fractional-part cube into `M ^ card ι` boxes and apply the
pigeonhole principle to one more multiple. The denominator and every coordinate
error are explicit, as required for the final reciprocal approximation argument.
-/

namespace BakerHarman

/-- Simultaneous approximation with denominator at most `M ^ card ι` and
coordinate error strictly less than `1 / M`. -/
theorem simultaneous_dirichlet {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (hM : 0 < M) :
    ∃ l : ℕ, 0 < l ∧ l ≤ M ^ Fintype.card ι ∧
      ∃ p : ι → ℤ, ∀ i, |(l : ℝ) * x i - (p i : ℝ)| < 1 / M := by
  classical
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  let f : Fin (M ^ Fintype.card ι + 1) → ι → Fin M := fun k i =>
    ⟨⌊(M : ℝ) * Int.fract ((k : ℕ) * x i)⌋₊,
      (Nat.floor_lt (mul_nonneg hM0.le (Int.fract_nonneg _))).mpr
        (by nlinarith [Int.fract_lt_one ((k : ℕ) * x i)])⟩
  have hcard : Fintype.card (ι → Fin M) < Fintype.card (Fin (M ^ Fintype.card ι + 1)) := by simp
  have hn := Fintype.not_injective_of_card_lt f hcard
  simp only [Function.Injective] at hn
  push Not at hn
  obtain ⟨u, v, huv, he⟩ : ∃ u v : Fin (M ^ Fintype.card ι + 1), u < v ∧ f u = f v := by
    obtain ⟨u, v, he, hne⟩ := hn
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨u, v, h, he⟩
    · exact ⟨v, u, h, he.symm⟩
  have huvNat : (u : ℕ) < v := huv
  refine ⟨(v : ℕ) - u, Nat.sub_pos_of_lt huvNat, by omega,
    fun i => ⌊(v : ℕ) * x i⌋ - ⌊(u : ℕ) * x i⌋, ?_⟩
  intro i
  have hf : ⌊(M : ℝ) * Int.fract ((u : ℕ) * x i)⌋₊ =
      ⌊(M : ℝ) * Int.fract ((v : ℕ) * x i)⌋₊ := congrArg Fin.val (congrFun he i)
  have hlu := Nat.floor_le (mul_nonneg hM0.le (Int.fract_nonneg ((u : ℕ) * x i)))
  have hlv := Nat.floor_le (mul_nonneg hM0.le (Int.fract_nonneg ((v : ℕ) * x i)))
  have hhu := Nat.lt_floor_add_one ((M : ℝ) * Int.fract ((u : ℕ) * x i))
  have hhv := Nat.lt_floor_add_one ((M : ℝ) * Int.fract ((v : ℕ) * x i))
  rw [hf] at hlu hhu
  have hbox : |(M : ℝ) * (Int.fract ((v : ℕ) * x i) - Int.fract ((u : ℕ) * x i))| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith only [hlu, hlv, hhu, hhv]
  rw [abs_mul, abs_of_pos hM0] at hbox
  have hfrac : |Int.fract ((v : ℕ) * x i) - Int.fract ((u : ℕ) * x i)| < 1 / M :=
    (lt_div_iff₀ hM0).mpr (by nlinarith only [hbox])
  convert hfrac using 1
  congr 1
  rw [Nat.cast_sub huvNat.le, Int.cast_sub]
  simp only [Int.fract]
  ring

end BakerHarman
