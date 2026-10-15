import BakerHarman.Lattice.Scaling
import BakerHarman.Defs

/-!
# The standard integer lattice in Euclidean space

Its covolume and minimum nonzero length are one. Scaling this lattice translates
unit-ball reciprocal approximation into equal coordinate tolerances.
-/

namespace BakerHarman

variable (ι : Type*) [Fintype ι]

noncomputable def coordinateLattice : Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis)

instance coordinateLattice_discrete : DiscreteTopology (coordinateLattice ι) := by
  unfold coordinateLattice; infer_instance

instance coordinateLattice_isZLattice : IsZLattice ℝ (coordinateLattice ι) := by
  unfold coordinateLattice; infer_instance

theorem mem_coordinateLattice (x : EuclideanSpace ℝ ι) :
    x ∈ coordinateLattice ι ↔ ∀ i, ∃ z : ℤ, x i = (z : ℝ) := by
  rw [coordinateLattice, Module.Basis.mem_span_iff_repr_mem]
  change (∀ i, ∃ z : ℤ, (z : ℝ) = x i) ↔ (∀ i, ∃ z : ℤ, x i = (z : ℝ))
  exact forall_congr' (fun _ => exists_congr (fun _ => eq_comm))

theorem coordinateLattice_separation :
    ∀ x ∈ coordinateLattice ι, x ≠ 0 → 1 ≤ ‖x‖ := by
  intro x hx hx0
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx0
    ext i
    exact h i
  obtain ⟨z, hz⟩ := (mem_coordinateLattice ι x).mp hx i
  have hz0 : z ≠ 0 := by intro he; simp only [he, Int.cast_zero] at hz; exact hi hz
  have hz1 : (1 : ℤ) ≤ |z| := by have := abs_pos.mpr hz0; omega
  have hxi : (1 : ℝ) ≤ ‖x i‖ := by rw [hz, Real.norm_eq_abs]; exact_mod_cast hz1
  exact hxi.trans (PiLp.norm_apply_le x i)

theorem coordinateLattice_covolume : ZLattice.covolume (coordinateLattice ι) = 1 := by
  classical
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let bZ := b.restrictScalars ℤ
  have he : bZ.ofZLatticeBasis ℝ (coordinateLattice ι) = b := by
    ext i : 1
    exact (bZ.ofZLatticeBasis_apply ℝ (coordinateLattice ι) i).trans (b.restrictScalars_apply ℤ i)
  have h := lattice_covolume_sq_eq_gram (coordinateLattice ι) bZ
  rw [he, show Matrix.gram ℝ b = 1 from
    Matrix.gram_eq_one_iff_orthonormal.mpr (EuclideanSpace.basisFun ι ℝ).orthonormal,
    Matrix.det_one] at h
  have hp := ZLattice.covolume_pos (coordinateLattice ι) MeasureTheory.volume
  nlinarith only [h, hp]

/-- A reciprocal approximation in a scaled coordinate lattice controls every
nearest-integer coordinate error. -/
theorem coordinateLattice_reciprocal_approximation (ρ : ℝ) (hρ : 0 < ρ)
    (r : ℝ) (a : EuclideanSpace ℝ ι)
    (h : ∃ v : scaledLattice (coordinateLattice ι) ρ hρ.ne',
      ‖r⁻¹ • (ρ • a) - (v : EuclideanSpace ℝ ι)‖ < 1) :
    ∀ i, distNearestInt (a i / r) ≤ ρ⁻¹ := by
  obtain ⟨v, hv⟩ := scaledLattice_reciprocal_approximation (coordinateLattice ι) ρ hρ r a h
  intro i
  obtain ⟨z, hz⟩ := (mem_coordinateLattice ι v).mp v.property i
  have hi := (PiLp.norm_apply_le (r⁻¹ • a - (v : EuclideanSpace ℝ ι)) i).trans_lt hv
  have habs : |a i / r - (z : ℝ)| ≤ ρ⁻¹ := by
    simpa only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, hz, Real.norm_eq_abs,
      div_eq_mul_inv, mul_comm] using hi.le
  exact (round_le (a i / r) z).trans habs

end BakerHarman
