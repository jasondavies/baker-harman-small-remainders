import BakerHarman.Lattice.Dual

/-!
# Euclidean characters and the Gaussian Fourier integral

Adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Combinatorics/Progressions/Fourier/MonomialCharacterMean.lean`.
Proofs are extracted into the project namespace with minimal imports.
Upstream code is licensed under Apache 2.0; see
`vendor/baker-harman-analytics/LICENSE`.
-/

section

namespace BakerHarman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def euclideanCharacter (ξ x : E) : ℂ :=
  fourier 1 ((inner ℝ ξ x : ℝ) : UnitAddCircle)

@[simp]
theorem euclideanCharacter_zero (ξ : E) : euclideanCharacter ξ 0 = 1 := by
  simp [euclideanCharacter]

@[simp]
theorem euclideanCharacter_add (ξ x y : E) :
    euclideanCharacter ξ (x + y) = euclideanCharacter ξ x * euclideanCharacter ξ y := by
  simp [euclideanCharacter, inner_add_right, AddCircle.toCircle_add]

@[simp]
theorem euclideanCharacter_neg (ξ x : E) :
    euclideanCharacter ξ (-x) = star (euclideanCharacter ξ x) := by
  simp only [euclideanCharacter, inner_neg_right, AddCircle.coe_neg, fourier_apply,
    one_zsmul, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  rfl

@[simp]
theorem norm_euclideanCharacter (ξ x : E) : ‖euclideanCharacter ξ x‖ = 1 := by
  simp [euclideanCharacter]

theorem continuous_euclideanCharacter (ξ : E) : Continuous (euclideanCharacter ξ) := by
  unfold euclideanCharacter
  fun_prop

theorem euclideanCharacter_eq_exp (ξ x : E) :
    euclideanCharacter ξ x = Complex.exp (2 * Real.pi * Complex.I * (inner ℝ ξ x : ℝ)) := by
  simpa only [euclideanCharacter, fourier_apply,
    one_zsmul, Int.cast_one, Complex.ofReal_one, mul_one, div_one] using
    (fourier_coe_apply (T := (1 : ℝ)) (n := 1) (x := inner ℝ ξ x))

theorem euclideanCharacter_on_lattice (Λ : Submodule ℤ E) (ξ : E)
    (hξ : ξ ∈ euclideanDualLattice Λ) (m : Λ) : euclideanCharacter ξ m = 1 := by
  obtain ⟨n, hn⟩ := (mem_euclideanDualLattice Λ ξ).mp hξ m m.property
  rw [euclideanCharacter, hn]
  have hnzero : (((n : ℝ) : UnitAddCircle)) = 0 := by
    exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨n, by simp⟩
  rw [hnzero, fourier_eval_zero]

theorem euclideanCharacter_sub_lattice (Λ : Submodule ℤ E) (ξ : E)
    (hξ : ξ ∈ euclideanDualLattice Λ) (x : E) (m : Λ) :
    euclideanCharacter ξ (x - m) = euclideanCharacter ξ x := by
  rw [sub_eq_add_neg, euclideanCharacter_add, euclideanCharacter_neg,
    euclideanCharacter_on_lattice Λ ξ hξ m, star_one, mul_one]

end BakerHarman

end

section

namespace BakerHarman

open MeasureTheory Real
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem gaussian_character_integrable {t : ℝ} (ht : 0 < t) (ξ : E) :
    Integrable (fun x : E => euclideanCharacter ξ x *
      (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ)) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < ((Real.pi * t : ℝ) : ℂ).re by simpa using mul_pos Real.pi_pos ht)
    (2 * Real.pi * Complex.I) ξ
  convert h using 1
  ext x
  rw [euclideanCharacter_eq_exp, Complex.exp_add]
  push_cast
  rw [mul_comm]
  simp only [neg_mul]

theorem gaussian_fourier_prefactor {t : ℝ} (ht : 0 < t) (d : ℕ) :
    ((Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ)) ^ ((d : ℂ) / 2) =
      (((Real.sqrt t) ^ d)⁻¹ : ℝ) := by
  have he : (Real.pi : ℂ) / ((Real.pi * t : ℝ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [he, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    ← Complex.ofReal_cpow (inv_nonneg.mpr ht.le), Real.inv_rpow ht.le]
  congr 2
  rw [show (d : ℝ) / 2 = (1 / 2 : ℝ) * d by ring,
    Real.rpow_mul_natCast ht.le, Real.sqrt_eq_rpow]

theorem gaussian_fourier_integral {t : ℝ} (ht : 0 < t) (ξ : E) :
    (∫ x : E, euclideanCharacter (-ξ) x * (Real.exp (-Real.pi * t * ‖x‖ ^ 2) : ℂ)) =
      ((((Real.sqrt t) ^ Module.finrank ℝ E)⁻¹ *
        Real.exp (-Real.pi / t * ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
  have h := fourier_gaussian_innerProductSpace
    (show 0 < ((Real.pi * t : ℝ) : ℂ).re by simpa using mul_pos Real.pi_pos ht) ξ
  rw [gaussian_fourier_prefactor ht] at h
  calc
    _ = 𝓕 (fun v : E => Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖v‖ ^ 2)) ξ := by
      simp only [fourier_eq', smul_eq_mul, euclideanCharacter_eq_exp, inner_neg_left]
      congr 1
      ext x
      rw [real_inner_comm x ξ]
      push_cast
      congr 2 <;> ring
    _ = _ := h
    _ = _ := by
      push_cast
      congr 1
      congr 1
      field_simp

end BakerHarman

end
