import BakerHarman.Lattice.OrthogonalBlockGram
import BakerHarman.Lattice.NormalHyperplaneProjection

/-!
# Covolumes of primitive lattice hyperplanes

The hyperplane calculation is adapted from `openai/math`, revision
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`lean/OAI/Combinatorics/Progressions/Lattices/LatticeSheetHaar.lean`.
Upstream code is licensed under Apache 2.0; see
`vendor/baker-harman-analytics/LICENSE`.
The Gram determinant identity is proved directly from Mathlib's covolume formula.
-/

namespace BakerHarman

open Module MeasureTheory OAI.Erdos3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lattice_covolume_sq_eq_gram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (b : Basis ι ℤ Λ) :
    ZLattice.covolume Λ ^ 2 = (Matrix.gram ℝ (b.ofZLatticeBasis ℝ Λ)).det := by
  classical
  let bR := b.ofZLatticeBasis ℝ Λ
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using finrank_eq_card_basis bR))
  have hv : volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume)]
    change (volume (parallelepiped o)).toReal = 1
    rw [o.volume_parallelepiped, ENNReal.toReal_one]
  have hc := ZLattice.covolume_eq_det_mul_measureReal Λ volume b o.toBasis
  rw [hv, mul_one] at hc
  have hg : Matrix.gram ℝ o.toBasis = 1 :=
    Matrix.gram_eq_one_iff_orthonormal.mpr o.orthonormal
  rw [gram_det_basis_change o.toBasis, hg, Matrix.det_one, mul_one, hc, sq_abs]
  congr 2
  ext i
  exact (b.ofZLatticeBasis_apply ℝ Λ i).symm

theorem latticeHyperplane_covolume_sq (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) :
    ZLattice.covolume Λ ^ 2 =
      ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) ^ 2 * (‖ξ‖⁻¹) ^ 2 := by
  classical
  let f := normalFunctional ξ
  let K := latticeHyperplane Λ f
  let : IsZLattice ℝ K := latticeHyperplane_isZLattice Λ f hint w hwΛ hw
  let bK := Module.Free.chooseBasis ℤ K
  let b := latticeHyperplaneBasis Λ f hint w hwΛ hw bK
  let bR := b.ofZLatticeBasis ℝ Λ
  let bKR := bK.ofZLatticeBasis ℝ K
  have hinl (i) : bR (Sum.inl i) = (bKR i : E) := by
    simpa only [bR, bKR, Module.Basis.ofZLatticeBasis_apply, b] using
      latticeHyperplaneBasis_inl Λ f hint w hwΛ hw bK i
  have hinr (j : Unit) : bR (Sum.inr j) = w := by
    simpa only [bR, Module.Basis.ofZLatticeBasis_apply, b] using
      latticeHyperplaneBasis_inr Λ f hint w hwΛ hw bK j
  have hspan : Submodule.span ℝ (Set.range (fun i => bR (Sum.inl i))) = f.ker := by
    rw [show (fun i => bR (Sum.inl i)) = (fun i => (bKR i : E)) from funext hinl]
    change Submodule.span ℝ (Set.range (f.ker.subtype ∘ bKR)) = _
    rw [Set.range_comp, ← Submodule.map_span, bKR.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hkernel : (Matrix.gram ℝ (fun i => bR (Sum.inl i))).det = ZLattice.covolume K ^ 2 := by
    have he : Matrix.gram ℝ (fun i => bR (Sum.inl i)) = Matrix.gram ℝ bKR := by
      ext i j
      simp only [Matrix.gram_apply, hinl]
      rfl
    rw [he]
    exact (lattice_covolume_sq_eq_gram K bK).symm
  have hblock := gram_det_orthogonal_block bR
  dsimp only at hblock
  rw [hspan, hkernel, Matrix.det_unique (n := Unit), Matrix.gram_apply, hinr,
    real_inner_self_eq_norm_sq, normalHyperplane_height ξ w hξ hw] at hblock
  rw [lattice_covolume_sq_eq_gram Λ b]
  exact hblock

theorem latticeHyperplane_covolume (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (ξ : E) (hξ : ξ ≠ 0)
    (hint : ∀ x ∈ Λ, ∃ n : ℤ, inner ℝ ξ x = (n : ℝ))
    (w : E) (hwΛ : w ∈ Λ) (hw : inner ℝ ξ w = 1) :
    ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) =
      ‖ξ‖ * ZLattice.covolume Λ := by
  let := latticeHyperplane_isZLattice Λ (normalFunctional ξ) hint w hwΛ hw
  have h := latticeHyperplane_covolume_sq Λ ξ hξ hint w hwΛ hw
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hc := ZLattice.covolume_pos Λ MeasureTheory.volume
  have hk := ZLattice.covolume_pos (latticeHyperplane Λ (normalFunctional ξ)) MeasureTheory.volume
  have hs : (‖ξ‖ * ZLattice.covolume Λ) ^ 2 =
      ZLattice.covolume (latticeHyperplane Λ (normalFunctional ξ)) ^ 2 := by
    rw [mul_pow, h]
    field_simp
  nlinarith [mul_pos hn hc]


end BakerHarman
