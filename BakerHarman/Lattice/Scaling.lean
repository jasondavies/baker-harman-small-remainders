import BakerHarman.Lattice.HyperplaneCovolume

/-!
# Scaling lattices

Positive homotheties multiply the minimum length by the scale and the covolume
by its dimension-th power. We use a pullback along the inverse homothety so that
Mathlib supplies the full-lattice and discreteness instances directly.
-/

namespace BakerHarman

open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def scaledLattice (Λ : Submodule ℤ E) (c : ℝ) (hc : c ≠ 0) : Submodule ℤ E :=
  ZLattice.comap ℝ Λ (LinearEquiv.smulOfNeZero ℝ E c hc).symm.toContinuousLinearEquiv.toLinearMap

instance scaledLattice_discrete (Λ : Submodule ℤ E) [DiscreteTopology Λ] (c : ℝ) (hc : c ≠ 0) :
    DiscreteTopology (scaledLattice Λ c hc) := by unfold scaledLattice; infer_instance

instance scaledLattice_isZLattice (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (c : ℝ) (hc : c ≠ 0) : IsZLattice ℝ (scaledLattice Λ c hc) := by
  unfold scaledLattice; infer_instance

@[simp] theorem mem_scaledLattice (Λ : Submodule ℤ E) (c : ℝ) (hc : c ≠ 0) (x : E) :
    x ∈ scaledLattice Λ c hc ↔ c⁻¹ • x ∈ Λ := Iff.rfl

@[simp] theorem smul_mem_scaledLattice (Λ : Submodule ℤ E) (c : ℝ) (hc : c ≠ 0) (x : E) :
    c • x ∈ scaledLattice Λ c hc ↔ x ∈ Λ := by
  rw [mem_scaledLattice, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem scaledLattice_separation (Λ : Submodule ℤ E) (c : ℝ) (hc : 0 < c)
    (ρ : ℝ) (hsep : ∀ x ∈ Λ, x ≠ 0 → ρ ≤ ‖x‖) :
    ∀ x ∈ scaledLattice Λ c hc.ne', x ≠ 0 → c * ρ ≤ ‖x‖ := by
  intro x hx hx0
  have h := hsep (c⁻¹ • x) ((mem_scaledLattice Λ c hc.ne' x).mp hx)
    (smul_ne_zero (inv_ne_zero hc.ne') hx0)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc] at h
  have hh := mul_le_mul_of_nonneg_left h hc.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hh

/-- Undo a positive scaling in a reciprocal approximation. -/
theorem scaledLattice_reciprocal_approximation (Λ : Submodule ℤ E)
    (c : ℝ) (hc : 0 < c) (r : ℝ) (y : E)
    (h : ∃ m : scaledLattice Λ c hc.ne', ‖r⁻¹ • (c • y) - (m : E)‖ < 1) :
    ∃ m : Λ, ‖r⁻¹ • y - (m : E)‖ < c⁻¹ := by
  obtain ⟨m, hm⟩ := h
  refine ⟨⟨c⁻¹ • (m : E), (mem_scaledLattice Λ c hc.ne' m).mp m.property⟩, ?_⟩
  change ‖r⁻¹ • y - c⁻¹ • (m : E)‖ < _
  have he : r⁻¹ • y - c⁻¹ • (m : E) = c⁻¹ • (r⁻¹ • (c • y) - (m : E)) := by
    rw [smul_sub, smul_comm r⁻¹ c, smul_smul c⁻¹ c, inv_mul_cancel₀ hc.ne', one_smul]
  rw [he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hm (inv_pos.mpr hc)

variable [MeasurableSpace E] [BorelSpace E]

theorem scaledLattice_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (c : ℝ) (hc : 0 < c) :
    ZLattice.covolume (scaledLattice Λ c hc.ne') = c ^ finrank ℝ E * ZLattice.covolume Λ := by
  classical
  let b := Free.chooseBasis ℤ Λ
  let bR := b.ofZLatticeBasis ℝ Λ
  let e := (LinearEquiv.smulOfNeZero ℝ E c hc.ne').symm
  let : DiscreteTopology (ZLattice.comap ℝ Λ e.toLinearMap) := scaledLattice_discrete Λ c hc.ne'
  let : IsZLattice ℝ (ZLattice.comap ℝ Λ e.toLinearMap) := scaledLattice_isZLattice Λ c hc.ne'
  let b' := b.ofZLatticeComap ℝ Λ e
  have he (i) : (b' i : E) = c • bR i := by
    simp only [b', Basis.ofZLatticeComap_apply, e, LinearEquiv.symm_symm,
      LinearEquiv.smulOfNeZero_apply, bR, Basis.ofZLatticeBasis_apply]
  have hd : bR.det ((↑) ∘ b') = c ^ finrank ℝ E := by
    rw [show ((↑) ∘ b' : _ → E) = (fun i => c • bR i) from funext he,
      bR.det.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ,
      ← finrank_eq_card_basis bR]
  have ho : ZLattice.covolume Λ = volume.real (ZSpan.fundamentalDomain bR) := by
    rw [ZLattice.covolume_eq_det_mul_measureReal Λ volume b bR]
    have heq : ((↑) ∘ b : _ → E) = bR := by ext i; exact (b.ofZLatticeBasis_apply ℝ Λ i).symm
    rw [heq, Basis.det_self, abs_one, one_mul]
  change ZLattice.covolume (ZLattice.comap ℝ Λ e.toLinearMap) = _
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume b' bR, hd,
    abs_of_pos (pow_pos hc _), ← ho]

end BakerHarman
