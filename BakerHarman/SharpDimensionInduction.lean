import BakerHarman.SlackDimensionOne
import BakerHarman.HyperplaneBudget
import BakerHarman.Lattice.HyperplaneTransfer

/-!
# Lattice approximation with the original logarithmic degrees

A strict power margin permits the lower-dimensional induction to use a slightly
larger exponent. Each projection therefore costs only one logarithm, even though
the Gaussian detection radius is logarithmic.
-/

namespace BakerHarman

universe u

open OAI.Erdos3

/-- Uniform lattice approximation statement, with explicit constants and
logarithmic degree for use in dimension induction. -/
def PowerLatticeStatement (d : ℕ) (K γ : ℝ) (m : ℕ) (A B Q₀ R₀ : ℝ) : Prop :=
  ∀ (R : ℝ), R₀ ≤ R → ∀ (Q : ℝ), Q₀ ≤ Q → Q ≤ R ^ γ →
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E],
  Module.finrank ℝ E = d → ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
  ∀ ρ : ℝ, 1 ≤ ρ → (∀ x ∈ Λ, x ≠ 0 → ρ ≤ ‖x‖) → ZLattice.covolume Λ ≤ Q →
  ∀ y : E, A * R * Q * (Real.log Q + 1) ^ (m + 1) ≤ ‖y‖ → ‖y‖ ≤ R ^ (K + 1) →
    ∃ r : ℤ, R ≤ r ∧ (r : ℝ) ≤ B * R * Q * (Real.log Q + 1) ^ m / ρ ∧
      ∃ v : Λ, ‖(r : ℝ)⁻¹ • y - (v : E)‖ < 1

theorem powerLatticeStatement_one (K : ℝ) (hK : 1 ≤ K) (γ : ℝ)
    (hγ : γ ≤ analyticPowerRange K) :
    ∃ A B Q₀ R₀ : ℝ, 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      PowerLatticeStatement.{u} 1 K γ 0 A B Q₀ R₀ := by
  obtain ⟨A, Q₀, R₀, hA, hQ₀, hR₀, hbase⟩ := bakerHarman_slack_dimension_one K hK
  refine ⟨A, 2 * latticeDimensionFactor 1, Q₀, R₀, hA,
    mul_pos (by norm_num) (latticeDimensionFactor_pos 1), hQ₀, hR₀, ?_⟩
  intro R hR Q hQ hQR E _ _ _ _ _ hdim Λ _ _ ρ hρ hsep hcov y hylo hyhi
  have hsep1 : ∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖ := fun x hx hx0 => hρ.trans (hsep x hx hx0)
  obtain ⟨r, hr, hr2, v, hv⟩ := hbase R hR Q hQ (hQR.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hγ)) E hdim Λ hsep1 hcov y
    (by simpa using hylo) hyhi
  refine ⟨r, hr, hr2.trans ?_, v, hv⟩
  simpa only [hdim, pow_zero, mul_one] using
    reciprocal_interval_le_covolume_separation Λ (by omega) ρ hρ hsep R Q (by linarith) hcov

set_option maxHeartbeats 400000 in
/-- With strict power slack, the successor step costs exactly one logarithm. -/
theorem powerLatticeStatement_succ (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 1 ≤ K)
    (γ γ' : ℝ) (hγ : 0 < γ) (hgap : γ < γ') (hγ' : γ' < analyticPowerRange K)
    (m : ℕ) (A B Q₀ R₀ : ℝ) (hA : 0 < A) (hB : 0 < B) (hQ₀ : 1 ≤ Q₀) (_hR₀ : 2 ≤ R₀)
    (ih : PowerLatticeStatement.{u} d K γ' m A B Q₀ R₀) :
    ∃ (A' B' Q₀' R₀' : ℝ), 0 < A' ∧ 0 < B' ∧ 1 ≤ Q₀' ∧ 2 ≤ R₀' ∧
      PowerLatticeStatement.{u} (d + 1) K γ (1 + m) A' B' Q₀' R₀' := by
  obtain ⟨C, Qs, Rs, hC, hQs, hRs, hsmall⟩ := bakerHarman_slack_small_dual_vector (d + 1) K hK
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
  let D := (c + 2) * C + 1
  let G := F * D
  have hD : 0 < D := by dsimp [D]; positivity
  have hG : 0 < G := mul_pos hF hD
  obtain ⟨q₁, hlogbudget⟩ := Filter.eventually_atTop.mp
    (log_add_one_pow_absorbed (F * C) 1 1 (by norm_num))
  obtain ⟨r₁, hpowerbudget⟩ := Filter.eventually_atTop.mp
    (log_add_one_pow_absorbed (F * C) (γ' - γ) 1 (sub_pos.mpr hgap))
  let A' := C / δ + A * G * 2 ^ (m + 1) + 1
  let B' := max (2 * latticeDimensionFactor (d + 1)) (B * G * 2 ^ m)
  have hA' : 0 < A' := by dsimp [A']; positivity
  have hB' : 0 < B' := lt_of_lt_of_le
    (mul_pos (by norm_num) (latticeDimensionFactor_pos _)) (le_max_left _ _)
  refine ⟨A', B', max Qs q₁, max (max Rs R₀) r₁, hA', hB',
    hQs.trans (le_max_left _ _), hRs.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro R hR Q hQ hQR E _ _ _ _ _ hdim Λ _ _ ρ hρ hsep hcov y hylo hyhi
  have hRsmall : Rs ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hRprev : R₀ ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
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
    have hmul : 2 * latticeDimensionFactor (d + 1) ≤ B' * L ^ (1 + m) :=
      (le_max_left _ _).trans (le_mul_of_one_le_right hB'.le (one_le_pow₀ hL1))
    exact hi.trans (div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_right hmul (mul_nonneg hR0.le hQ0.le)]) hρ0.le)
  push Not at hnear
  obtain ⟨ξ, hξΛ, hξ, hξnorm, hξinner⟩ :=
    hsmall R hRsmall Q hQsmall (hQR.trans (Real.rpow_le_rpow_of_exponent_le
      (by linarith) (hgap.trans hγ').le)) E hdim Λ hsep1 hcov y hyhi hnear
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
  let R' := D * R / ‖p‖ * L ^ 1
  let Q' := F * ‖p‖ * Q
  have hQ'lo : Q₀ ≤ Q' := by
    exact hFδ.trans (by dsimp [Q']; nlinarith [mul_le_mul_of_nonneg_left hpδ hF.le])
  have hQ'1 : 1 ≤ Q' := hQ₀.trans hQ'lo
  have hQ'0 : 0 < Q' := by linarith
  have hscale : c * R ≤ R' := by
    dsimp [R']
    rw [pow_one, div_mul_eq_mul_div, le_div_iff₀ hp0]
    have hh := mul_le_mul_of_nonneg_left hpC (show 0 ≤ c * R by positivity)
    have hcoef : c * C ≤ D := by dsimp only [D]; nlinarith only [hC, mul_nonneg hc.le hC.le]
    nlinarith only [hh, mul_le_mul_of_nonneg_right hcoef (mul_nonneg hR0.le hL.le)]
  have herrorScale : 2 * C * R * L / ‖p‖ ≤ R' := by
    dsimp [R']
    rw [pow_one, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hp0]
    have hcoef : 2 * C ≤ D := by dsimp only [D]; nlinarith only [mul_nonneg hc.le hC.le]
    nlinarith only [mul_le_mul_of_nonneg_right hcoef (mul_nonneg hR0.le hL.le)]
  have hRR' : R ≤ R' := (le_mul_of_one_le_left hR0.le hc1).trans hscale
  have hR'0 : 0 < R' := hR0.trans_le hRR'
  have hprod : R' * Q' = G * R * Q * L ^ 1 := by
    dsimp [R', Q', G]; field_simp
  have hQleR : Q ≤ R := hQR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ R by linarith) ((hgap.trans hγ').le.trans (analyticPowerRange_le_one K)))
  have hlogs : L ≤ Real.log R + 1 := by
    dsimp [L]; linarith [Real.log_le_log hQ0 hQleR]
  have hpower : Q' ≤ R' ^ γ' := by
    have hb := hpowerbudget R ((le_max_right _ _).trans hR)
    simp only [pow_one] at hb
    have hFC : F * C * L ≤ R ^ (γ' - γ) :=
      (mul_le_mul_of_nonneg_left hlogs (mul_nonneg hF.le hC.le)).trans hb
    calc
      Q' ≤ (F * C * L) * Q := by
        dsimp only [Q']; nlinarith only [mul_le_mul_of_nonneg_left hpC (mul_nonneg hF.le hQ0.le)]
      _ ≤ R ^ (γ' - γ) * R ^ γ := mul_le_mul hFC hQR hQ0.le (by positivity)
      _ = R ^ γ' := by rw [← Real.rpow_add hR0]; congr 1; ring
      _ ≤ R' ^ γ' := Real.rpow_le_rpow hR0.le hRR' (hγ.trans hgap).le
  have hlog : Real.log Q' + 1 ≤ 2 * L := by
    have hb := hlogbudget Q ((le_max_right _ _).trans hQ)
    simp only [pow_one, Real.rpow_one] at hb
    have hbound : Q' ≤ Q ^ 2 := by
      dsimp only [Q']; nlinarith only [mul_le_mul_of_nonneg_left hpC (mul_nonneg hF.le hQ0.le), mul_le_mul_of_nonneg_right hb hQ0.le]
    have hh := Real.log_le_log hQ'0 hbound
    rw [Real.log_pow] at hh
    dsimp [L]; norm_num at hh; linarith
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
    apply hyperplane_projected_lower_budget R Q R' Q' G c (C / δ) A' A ‖y‖ ‖z‖
      L (Real.log Q' + 1) 1 (m + 1) hR0.le hQ0.le hG.le hc1 (by positivity) hA.le
      (norm_nonneg _) hL1 (by linarith [Real.log_nonneg hQ'1]) (by omega) hlog hprod
      (by dsimp [A']; linarith)
    · simpa only [Nat.add_assoc] using hylo
    · exact herror
  obtain ⟨r, hr, hrupper, v, hv⟩ := ih R' (hRprev.trans hRR') Q' hQ'lo hpower V hVdim
    Γ' ρ hρ hsep' hcov' (c • z) hzlower hzupper
  refine ⟨r, hRR'.trans hr, ?_, ?_⟩
  · have hlogprod := hyperplane_log_product_bound R Q R' Q' G L (Real.log Q' + 1) 1 m
      hR0.le hQ0.le hG.le hL.le (by linarith [Real.log_nonneg hQ'1]) hlog hprod
    have hh := mul_le_mul_of_nonneg_left hlogprod hB.le
    have hcoef : B * G * 2 ^ m ≤ B' := le_max_right _ _
    apply hrupper.trans
    apply div_le_div_of_nonneg_right _ hρ0.le
    nlinarith only [hh, mul_le_mul_of_nonneg_right hcoef
      (show 0 ≤ R * Q * L ^ (1 + m) by positivity)]
  · apply reciprocal_latticeHyperplane_transfer Λ p y hp c hc2 r (hR'0.trans_le hr)
    · have he : |inner ℝ p y| / ‖p‖ ≤ C * R * L / ‖p‖ :=
        div_le_div_of_nonneg_right hpinner' hp0.le
      change 2 * C * R * L / ‖p‖ ≤ R' at herrorScale
      have he2 : 2 * (C * R * L / ‖p‖) ≤ R' := by
        convert herrorScale using 1; ring
      linarith only [he, he2, hr]
    · exact ⟨v, hv⟩

/-- The lattice theorem with logarithmic degrees `d` and `d-1`, valid throughout
any strict subrange of the retained analytic power range. -/
theorem bakerHarman_sharp_lattice_approximation (d : ℕ) (hd : 0 < d)
    (K : ℝ) (hK : 1 ≤ K) (γ : ℝ) (hγ : 0 < γ) (hγupper : γ < analyticPowerRange K) :
    ∃ (A B Q₀ R₀ : ℝ), 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      PowerLatticeStatement.{u} d K γ (d - 1) A B Q₀ R₀ := by
  have hall : ∀ t : ℕ, ∀ γ : ℝ, 0 < γ → γ < analyticPowerRange K →
      ∃ (A B Q₀ R₀ : ℝ), 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
        PowerLatticeStatement.{u} (t + 1) K γ t A B Q₀ R₀ := by
    intro t
    induction t with
    | zero =>
      intro γ _ hγu
      exact powerLatticeStatement_one.{u} K hK γ hγu.le
    | succ t ih =>
      intro γ hγ hγu
      let γ' := (γ + analyticPowerRange K) / 2
      have hgap : γ < γ' := by dsimp [γ']; linarith
      have hγ' : γ' < analyticPowerRange K := by dsimp [γ']; linarith
      obtain ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩ := ih γ' (hγ.trans hgap) hγ'
      simpa only [Nat.add_comm 1] using powerLatticeStatement_succ (t + 1) (by omega)
        K hK γ γ' hγ hgap hγ' t A B Q₀ R₀ hA hB hQ₀ hR₀ h
  cases d with
  | zero => omega
  | succ t => simpa using hall t γ hγ hγupper

end BakerHarman
