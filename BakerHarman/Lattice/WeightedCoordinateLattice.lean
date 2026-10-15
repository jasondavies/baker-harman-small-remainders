import BakerHarman.Lattice.CoordinateLattice

/-! Diagonal coordinate lattices for unequal reciprocal tolerances. -/

namespace BakerHarman

open Module MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def weightedCoordinateBasis (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) :
    Basis ι ℝ (EuclideanSpace ℝ ι) :=
  (EuclideanSpace.basisFun ι ℝ).toBasis.unitsSMul
    (fun i => Units.mk0 (ψ i)⁻¹ (inv_ne_zero (hψ i).ne'))

lemma weightedCoordinateBasis_apply (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) (i : ι) :
    weightedCoordinateBasis ψ hψ i = (ψ i)⁻¹ • EuclideanSpace.basisFun ι ℝ i := by
  simp [weightedCoordinateBasis, Basis.unitsSMul_apply, Units.smul_def]

lemma weightedCoordinateBasis_repr (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    (weightedCoordinateBasis ψ hψ).repr x i = ψ i * x i := by
  change (weightedCoordinateBasis ψ hψ).coord i x = _
  simp [weightedCoordinateBasis, Basis.coord_unitsSMul, Units.smul_def,
    Basis.coord_apply]

noncomputable def weightedCoordinateLattice (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) :
    Submodule ℤ (EuclideanSpace ℝ ι) :=
  Submodule.span ℤ (Set.range (weightedCoordinateBasis ψ hψ))

instance weightedCoordinateLattice_discrete (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) :
    DiscreteTopology (weightedCoordinateLattice ψ hψ) := by
  unfold weightedCoordinateLattice; infer_instance

instance weightedCoordinateLattice_isZLattice (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) :
    IsZLattice ℝ (weightedCoordinateLattice ψ hψ) := by
  unfold weightedCoordinateLattice; infer_instance

lemma mem_weightedCoordinateLattice (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i)
    (x : EuclideanSpace ℝ ι) :
    x ∈ weightedCoordinateLattice ψ hψ ↔ ∀ i, ∃ z : ℤ, ψ i * x i = (z : ℝ) := by
  rw [weightedCoordinateLattice, Basis.mem_span_iff_repr_mem]
  simp only [weightedCoordinateBasis_repr]
  exact forall_congr' (fun i => exists_congr (fun z => eq_comm))

lemma weightedCoordinateLattice_separation (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i)
    (ρ : ℝ) (_hρ : 0 ≤ ρ) (hbound : ∀ i, ρ * ψ i ≤ 1) :
    ∀ x ∈ weightedCoordinateLattice ψ hψ, x ≠ 0 → ρ ≤ ‖x‖ := by
  intro x hx hx0
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (by ext i; exact h i)
  obtain ⟨z, hz⟩ := (mem_weightedCoordinateLattice ψ hψ x).mp hx i
  have hz0 : z ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at hz
    exact hi ((mul_eq_zero.mp hz).resolve_left (hψ i).ne')
  have hz1 : (1 : ℤ) ≤ |z| := by have := abs_pos.mpr hz0; omega
  have hxi : 1 ≤ ψ i * ‖x i‖ := by
    have hh : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast hz1
    rw [← hz, abs_mul, abs_of_pos (hψ i)] at hh
    simpa only [Real.norm_eq_abs] using hh
  have hnorm : ρ ≤ ‖x i‖ := by
    nlinarith only [hbound i, hxi, hψ i]
  exact hnorm.trans (PiLp.norm_apply_le x i)

lemma weightedCoordinateLattice_covolume (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) :
    ZLattice.covolume (weightedCoordinateLattice ψ hψ) = (∏ i, ψ i)⁻¹ := by
  classical
  let b₀ := (EuclideanSpace.basisFun ι ℝ).toBasis
  let b := weightedCoordinateBasis ψ hψ
  let bZ : Basis ι ℤ (weightedCoordinateLattice ψ hψ) := b.restrictScalars ℤ
  let b₀Z : Basis ι ℤ (coordinateLattice ι) := b₀.restrictScalars ℤ
  have hvol : volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    have h := ZLattice.covolume_eq_det_mul_measureReal (coordinateLattice ι) volume b₀Z b₀
    have he : ((↑) ∘ b₀Z : ι → EuclideanSpace ℝ ι) = b₀ := by
      ext i : 1; exact b₀.restrictScalars_apply ℤ i
    rw [he, Basis.det_self, abs_one, one_mul, coordinateLattice_covolume] at h
    exact h.symm
  have he : ((↑) ∘ bZ : ι → EuclideanSpace ℝ ι) =
      fun i => (ψ i)⁻¹ • b₀ i := by
    ext i : 1
    exact (b.restrictScalars_apply ℤ i).trans (weightedCoordinateBasis_apply ψ hψ i)
  rw [ZLattice.covolume_eq_det_mul_measureReal (weightedCoordinateLattice ψ hψ) volume bZ b₀, he,
    b₀.det.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one, hvol, mul_one,
    abs_of_pos (Finset.prod_pos (fun i _ => inv_pos.mpr (hψ i))), Finset.prod_inv_distrib]

/-- Unit-ball approximation in the diagonal lattice yields separate coordinate tolerances. -/
lemma weightedCoordinateLattice_reciprocal_approximation (ψ : ι → ℝ)
    (hψ : ∀ i, 0 < ψ i) (r : ℝ) (a : ι → ℝ)
    (h : ∃ v : weightedCoordinateLattice ψ hψ,
      ‖r⁻¹ • WithLp.toLp 2 (fun i => a i / ψ i) - (v : EuclideanSpace ℝ ι)‖ < 1) :
    ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨v, hv⟩ := h
  intro i
  obtain ⟨z, hz⟩ := (mem_weightedCoordinateLattice ψ hψ v).mp v.property i
  have hi := (PiLp.norm_apply_le
    (r⁻¹ • WithLp.toLp 2 (fun i => a i / ψ i) - (v : EuclideanSpace ℝ ι)) i).trans_lt hv
  have hh := mul_lt_mul_of_pos_left hi (hψ i)
  have he : ψ i * ‖(r⁻¹ • WithLp.toLp 2 (fun i => a i / ψ i) -
      (v : EuclideanSpace ℝ ι)) i‖ = |a i / r - (z : ℝ)| := by
    change ψ i * |r⁻¹ * (a i / ψ i) - (v : EuclideanSpace ℝ ι) i| = _
    calc
      _ = |ψ i * (r⁻¹ * (a i / ψ i) - (v : EuclideanSpace ℝ ι) i)| := by
        rw [abs_mul, abs_of_pos (hψ i)]
      _ = _ := by
        congr 1
        rw [mul_sub, hz]
        field_simp [(hψ i).ne']
  rw [he, mul_one] at hh
  exact (round_le (a i / r) z).trans hh.le

end BakerHarman
