import BakerHarman.DimensionOne
import BakerHarman.HyperplaneBudget
import BakerHarman.Lattice.HyperplaneTransfer

/-!
# Reciprocal approximation by dimension induction

The logarithmic exponent is allowed to depend on the dimension and the fixed
power exponent. The power range itself remains `Q ≤ R ^ gammaBH K`.
-/

namespace BakerHarman

universe u

open OAI.Erdos3

/-- Uniform lattice approximation statement, with explicit constants and
logarithmic degree for use in dimension induction. -/
def ReciprocalLatticeStatement (d : ℕ) (K : ℝ) (m : ℕ) (A B Q₀ R₀ : ℝ) : Prop :=
  ∀ (R : ℝ), R₀ ≤ R → ∀ (Q : ℝ), Q₀ ≤ Q → Q ≤ R ^ gammaBH K →
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E],
  Module.finrank ℝ E = d → ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
  ∀ ρ : ℝ, 1 ≤ ρ → (∀ x ∈ Λ, x ≠ 0 → ρ ≤ ‖x‖) → ZLattice.covolume Λ ≤ Q →
  ∀ y : E, A * R * Q * (Real.log Q + 1) ^ (m + 1) ≤ ‖y‖ → ‖y‖ ≤ R ^ (K + 1) →
    ∃ r : ℤ, R ≤ r ∧ (r : ℝ) ≤ B * R * Q * (Real.log Q + 1) ^ m / ρ ∧
      ∃ v : Λ, ‖(r : ℝ)⁻¹ • y - (v : E)‖ < 1

theorem reciprocalLatticeStatement_one (K : ℝ) (hK : 1 ≤ K) :
    ∃ A B Q₀ R₀ : ℝ, 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ReciprocalLatticeStatement.{u} 1 K 0 A B Q₀ R₀ := by
  obtain ⟨A, Q₀, R₀, hA, hQ₀, hR₀, hbase⟩ := bakerHarman_dimension_one K hK
  refine ⟨A, 2 * latticeDimensionFactor 1, Q₀, R₀, hA,
    mul_pos (by norm_num) (latticeDimensionFactor_pos 1), hQ₀, hR₀, ?_⟩
  intro R hR Q hQ hQR E _ _ _ _ _ hdim Λ _ _ ρ hρ hsep hcov y hylo hyhi
  have hsep1 : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖ := fun x hx hx0 => hρ.trans (hsep x hx hx0)
  obtain ⟨r, hr, hr2, v, hv⟩ := hbase R hR Q hQ hQR E hdim Λ hsep1 hcov y
    (by simpa using hylo) hyhi
  refine ⟨r, hr, hr2.trans ?_, v, hv⟩
  simpa only [hdim, pow_zero, mul_one] using
    reciprocal_interval_le_covolume_separation Λ (by omega) ρ hρ hsep R Q (by linarith) hcov

set_option maxHeartbeats 400000 in
/-- The successor step keeps the original power exponent; only the constants
and logarithmic degree increase. -/
theorem reciprocalLatticeStatement_succ (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 1 ≤ K)
    (m : ℕ) (A B Q₀ R₀ : ℝ) (hA : 0 < A) (hB : 0 < B) (hQ₀ : 1 ≤ Q₀) (_hR₀ : 2 ≤ R₀)
    (ih : ReciprocalLatticeStatement.{u} d K m A B Q₀ R₀) :
    ∃ (m' : ℕ) (A' B' Q₀' R₀' : ℝ), 0 < A' ∧ 0 < B' ∧ 1 ≤ Q₀' ∧ 2 ≤ R₀' ∧
      ReciprocalLatticeStatement.{u} (d + 1) K m' A' B' Q₀' R₀' := by
  obtain ⟨C, Qs, Rs, hC, hQs, hRs, hsmall⟩ := bakerHarman_small_dual_vector (d + 1) K hK
  let δ := Real.exp (-Real.pi) / latticeDimensionFactor (d + 1)
  have hδ : 0 < δ := div_pos (Real.exp_pos _) (latticeDimensionFactor_pos _)
  let c := max 2 (Q₀ / δ)
  have hc2 : 2 ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := by linarith
  have hc : 0 < c := by linarith
  let F := c ^ d
  have hF : 0 < F := pow_pos hc _
  have hcF : c ≤ F := le_self_pow₀ hc1 (Nat.ne_of_gt hd)
  have hFδ : Q₀ ≤ F * δ := by
    have hh : Q₀ ≤ c * δ := (div_le_iff₀ hδ).mp (le_max_right _ _)
    exact hh.trans (mul_le_mul_of_nonneg_right hcF hδ.le)
  obtain ⟨J, hJ, hbudget⟩ := exists_hyperplane_log_budget (gammaBH K) (gammaBH_pos K)
  obtain ⟨q₁, hbudget⟩ := Filter.eventually_atTop.mp (hbudget F C c hF hC hc)
  let A' := C / δ + A * F * 2 ^ (m + 1) + 1
  let B' := max (2 * latticeDimensionFactor (d + 1)) (B * F * 2 ^ m)
  have hA' : 0 < A' := by dsimp [A']; positivity
  have hB' : 0 < B' := lt_of_lt_of_le
    (mul_pos (by norm_num) (latticeDimensionFactor_pos _)) (le_max_left _ _)
  refine ⟨J + m, A', B', max Qs q₁, max Rs R₀, hA', hB',
    hQs.trans (le_max_left _ _), hRs.trans (le_max_left _ _), ?_⟩
  intro R hR Q hQ hQR E _ _ _ _ _ hdim Λ _ _ ρ hρ hsep hcov y hylo hyhi
  have hRsmall : Rs ≤ R := (le_max_left _ _).trans hR
  have hRprev : R₀ ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hQsmall : Qs ≤ Q := (le_max_left _ _).trans hQ
  have hQ1 : 1 ≤ Q := hQs.trans hQsmall
  have hQ0 : 0 < Q := by linarith
  let L := Real.log Q + 1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hQ1]
  have hL : 0 < L := by linarith
  have hρ0 : 0 < ρ := by linarith
  have hsep1 : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖ := fun x hx hx0 => hρ.trans (hsep x hx hx0)
  by_cases hnear : ∃ r : ℤ, R ≤ r ∧ (r : ℝ) ≤ 2 * R ∧
      ∃ v : Λ, ‖(r : ℝ)⁻¹ • y - (v : E)‖ < 1
  · obtain ⟨r, hr, hr2, v, hv⟩ := hnear
    refine ⟨r, hr, hr2.trans ?_, v, hv⟩
    have hi := reciprocal_interval_le_covolume_separation Λ (by omega) ρ hρ hsep R Q hR0.le hcov
    rw [hdim] at hi
    have hmul : 2 * latticeDimensionFactor (d + 1) ≤ B' * L ^ (J + m) :=
      (le_max_left _ _).trans (le_mul_of_one_le_right hB'.le (one_le_pow₀ hL1))
    exact hi.trans (div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_right hmul (mul_nonneg hR0.le hQ0.le)]) hρ0.le)
  push Not at hnear
  obtain ⟨ξ, hξΛ, hξ, hξnorm, hξinner⟩ :=
    hsmall R hRsmall Q hQsmall hQR E hdim Λ hsep1 hcov y hyhi hnear
  obtain ⟨p, w, hpΛ, hp, hpnorm, hpinner, hwΛ, hw⟩ :=
    exists_primitive_dual_vector Λ ξ hξΛ hξ y
  have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hpC : ‖p‖ ≤ C * L := hpnorm.trans hξnorm
  have hpinner' : |inner ℝ p y| ≤ C * R * L := hpinner.trans hξinner
  have hpδ : δ ≤ ‖p‖ * Q := by
    have hh : δ ≤ ‖p‖ * ZLattice.covolume Λ := by
      simpa only [hdim, δ, latticeDimensionFactor] using
        dual_norm_mul_covolume_lower_bound Λ hsep1 p hpΛ hp
    exact hh.trans (mul_le_mul_of_nonneg_left hcov hp0.le)
  let V := (normalFunctional p).ker
  let Γ := latticeHyperplane Λ (normalFunctional p)
  have hint := (mem_euclideanDualLattice Λ p).mp hpΛ
  let : IsZLattice ℝ Γ := latticeHyperplane_isZLattice Λ (normalFunctional p) hint w hwΛ hw
  have hVdim : Module.finrank ℝ V = d := by
    have hh := normalHyperplane_finrank p hp
    change Module.finrank ℝ V + 1 = Module.finrank ℝ E at hh
    omega
  let z : V := V.orthogonalProjectionOnto y
  let Γ' := scaledLattice Γ c hc.ne'
  let R' := R / ‖p‖ * L ^ J
  let Q' := F * ‖p‖ * Q
  have hQ'lo : Q₀ ≤ Q' := by
    exact hFδ.trans (by dsimp [Q']; nlinarith [mul_le_mul_of_nonneg_left hpδ hF.le])
  have hQ'1 : 1 ≤ Q' := hQ₀.trans hQ'lo
  have hQ'0 : 0 < Q' := by linarith
  obtain ⟨_, hs, hpow, hl⟩ := hbudget Q ((le_max_right _ _).trans hQ)
  obtain ⟨hscale, herrorScale, hpower, hlog⟩ := hyperplane_rescaling_bounds
    (gammaBH K) R Q ‖p‖ F C c J (gammaBH_pos K) hR0 hQ1 hp0 hF hC hc hQR hpC hs hpow hl
  change c * R ≤ R' at hscale
  have hRR' : R ≤ R' := (le_mul_of_one_le_left hR0.le hc1).trans hscale
  have hR'0 : 0 < R' := hR0.trans_le hRR'
  have hprod : R' * Q' = F * R * Q * L ^ J := by
    dsimp [R', Q']; field_simp
  have hcov' : ZLattice.covolume Γ' ≤ Q' := by
    rw [show Γ' = scaledLattice (latticeHyperplane Λ (normalFunctional p)) c hc.ne' from rfl,
      scaled_latticeHyperplane_covolume Λ p hp hint w hwΛ hw c hc, hdim, Nat.add_sub_cancel]
    change c ^ d * ‖p‖ * ZLattice.covolume Λ ≤ c ^ d * ‖p‖ * Q
    exact mul_le_mul_of_nonneg_left hcov (by positivity)
  have hsepΓ : ∀ x ∈ Γ, x ≠ 0 → ρ ≤ ‖x‖ := by
    intro x hx hx0
    exact hsep (x : E) hx (by intro he; apply hx0; exact Subtype.ext he)
  have hsep' : ∀ x ∈ Γ', x ≠ 0 → ρ ≤ ‖x‖ := by
    intro x hx hx0
    exact (le_mul_of_one_le_left hρ0.le hc1).trans (scaledLattice_separation Γ c hc ρ hsepΓ x hx hx0)
  have hznorm : ‖z‖ ≤ ‖y‖ := V.norm_orthogonalProjectionOnto_apply_le y
  have hzupper : ‖c • z‖ ≤ R' ^ (K + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact (mul_le_mul_of_nonneg_left (hznorm.trans hyhi) hc.le).trans
      (hyperplane_scaled_growth c R R' (K + 1) hc1 hR0.le (by linarith) hscale)
  have herror : ‖y‖ ≤ ‖z‖ + C / δ * R * Q * L := by
    have he := norm_le_normalHyperplane_projection_add p y hp
    have hb := hyperplane_error_budget (|inner ℝ p y|) ‖p‖ δ C R Q L
      hp0 hδ hC.le hR0.le hL.le hpδ hpinner'
    exact he.trans (add_le_add le_rfl hb)
  have hzlower : A * R' * Q' * (Real.log Q' + 1) ^ (m + 1) ≤ ‖c • z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    apply hyperplane_projected_lower_budget R Q R' Q' F c (C / δ) A' A ‖y‖ ‖z‖
      L (Real.log Q' + 1) J (m + 1) hR0.le hQ0.le hF.le hc1 (by positivity) hA.le
      (norm_nonneg _) hL1 (by linarith [Real.log_nonneg hQ'1]) (by omega) hlog hprod
      (by dsimp [A']; linarith)
    · simpa only [Nat.add_assoc] using hylo
    · exact herror
  obtain ⟨r, hr, hrupper, v, hv⟩ := ih R' (hRprev.trans hRR') Q' hQ'lo hpower V hVdim
    Γ' ρ hρ hsep' hcov' (c • z) hzlower hzupper
  refine ⟨r, hRR'.trans hr, ?_, ?_⟩
  · have hlogprod := hyperplane_log_product_bound R Q R' Q' F L (Real.log Q' + 1) J m
      hR0.le hQ0.le hF.le hL.le (by linarith [Real.log_nonneg hQ'1]) hlog hprod
    have hh := mul_le_mul_of_nonneg_left hlogprod hB.le
    have hcoef : B * F * 2 ^ m ≤ B' := le_max_right _ _
    apply hrupper.trans
    apply div_le_div_of_nonneg_right _ hρ0.le
    nlinarith only [hh, mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ R * Q * L ^ (J + m) by positivity)]
  · apply reciprocal_latticeHyperplane_transfer Λ p y hp c hc2 r (hR'0.trans_le hr)
    · have he : |inner ℝ p y| / ‖p‖ ≤ C * R * L / ‖p‖ :=
        div_le_div_of_nonneg_right hpinner' hp0.le
      change 2 * C * R * L / ‖p‖ ≤ R' at herrorScale
      have he2 : 2 * (C * R * L / ‖p‖) ≤ R' := by
        convert herrorScale using 1; ring
      linarith only [he, he2, hr]
    · exact ⟨v, hv⟩

/-- Reciprocal approximation for large vectors in every positive dimension.
The logarithmic degree and constants depend only on `d` and `K`. -/
theorem bakerHarman_lattice_approximation (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 1 ≤ K) :
    ∃ (m : ℕ) (A B Q₀ R₀ : ℝ), 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ReciprocalLatticeStatement.{u} d K m A B Q₀ R₀ := by
  have hall : ∀ t : ℕ, ∃ (m : ℕ) (A B Q₀ R₀ : ℝ),
      0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ReciprocalLatticeStatement.{u} (t + 1) K m A B Q₀ R₀ := by
    intro t
    induction t with
    | zero =>
      obtain ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩ := reciprocalLatticeStatement_one.{u} K hK
      exact ⟨0, A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩
    | succ t ih =>
      obtain ⟨m, A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩ := ih
      exact reciprocalLatticeStatement_succ (t + 1) (by omega) K hK m A B Q₀ R₀ hA hB hQ₀ hR₀ h
  cases d with
  | zero => omega
  | succ t => exact hall t

end BakerHarman
