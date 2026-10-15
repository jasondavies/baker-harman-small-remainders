import BakerHarman.ReciprocalDetection

/-!
# A short dual vector from failed reciprocal approximation

Combining Gaussian detection, reciprocal-sum estimates, and dyadic selection
produces a nonzero dual vector with a small scalar product. All constants are
chosen before the ambient space and lattice, as required for dimension induction.
-/

namespace BakerHarman

open OAI.Problem337 Classical

/-- If the reciprocal orbit avoids the unit neighborhoods of a separated
lattice, there is a short dual vector with scalar product `O(R(log Q+1))`.
The thresholds and constants depend only on `d` and `K`. -/
theorem bakerHarman_small_dual_vector (d : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C Q₀ R₀ : ℝ, 0 < C ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (Q : ℝ), Q₀ ≤ Q → Q ≤ R ^ gammaBH K →
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E],
      Module.finrank ℝ E = d → ∀ (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ],
      (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ‖x‖) → ZLattice.covolume Λ ≤ Q → ∀ y : E,
      ‖y‖ ≤ R ^ (K + 1) →
      (∀ r : ℤ, R ≤ r → (r : ℝ) ≤ 2 * R → ∀ m : Λ, 1 ≤ ‖(r : ℝ)⁻¹ • y - (m : E)‖) →
      ∃ p : E, p ∈ euclideanDualLattice Λ ∧ p ≠ 0 ∧
        ‖p‖ ≤ C * (Real.log Q + 1) ∧ |inner ℝ p y| ≤ C * R * (Real.log Q + 1) := by
  obtain ⟨A, hA, hsum⟩ := bakerHarman_large_sum_frequency_log_factor K hK
  let B : ℝ := 8 * ((d : ℝ) + 1)
  let D : ℝ := 2 * Real.exp Real.pi * B ^ d
  let M : ℝ := 2 + (11 / 10 : ℝ) / Real.log 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hM : 0 < M := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [M]; positivity
  obtain ⟨q₁, hdetect⟩ := Filter.eventually_atTop.mp (gaussian_lattice_detection d)
  obtain ⟨q₂, hremove⟩ := Filter.eventually_atTop.mp
    (large_terms_retain_mass_log_factor D (1 / 8) d (by norm_num))
  obtain ⟨r₁, hsum⟩ := Filter.eventually_atTop.mp (hsum B 1)
  let C : ℝ := 2 * B + 128 * A * M
  refine ⟨C, max 1 (max q₁ q₂), max 2 r₁, by dsimp [C]; positivity,
    le_max_left _ _, le_max_left _ _, ?_⟩
  intro R hR Q hQ hQR E _ _ _ _ _ hdim Λ _ _ hsep hcov y hy hfar
  have hR2 : 2 ≤ R := (le_max_left _ _).trans hR
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hQ
  have hQ0 : 0 < Q := by linarith
  have hq₁ : q₁ ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hq₂ : q₂ ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hr₁ : r₁ ≤ R := (le_max_right _ _).trans hR
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hQleR : Q ≤ R := hQR.trans (by
    calc
      R ^ gammaBH K ≤ R ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by linarith [gammaBH_le K])
      _ = R := Real.rpow_one R)
  have hlogs : Real.log Q ≤ Real.log R := Real.log_le_log hQ0 hQleR
  obtain ⟨L, U, hL, hU, hcardlo, hcardhi⟩ := exists_reciprocal_interval R hR2
  obtain ⟨hcount, hmass⟩ := hdetect Q hq₁ E hdim Λ hsep hcov ℤ (Finset.Icc L U)
    (fun r => (r : ℝ)⁻¹ • y) (by
      intro r hr
      obtain ⟨hrL, hrU⟩ := Finset.mem_Icc.mp hr
      have hrU' : (r : ℝ) ≤ U := by exact_mod_cast hrU
      exact hfar r (hL.trans (by exact_mod_cast hrL)) (hrU'.trans hU))
  let S := (dualBall Λ (detectionTemperature d Q)).erase 0
  let z : euclideanDualLattice Λ → ℝ := fun ξ => inner ℝ (ξ : E) y
  let w : euclideanDualLattice Λ → ℝ := fun ξ =>
    ‖∑ r ∈ Finset.Icc L U, differencingPhase (z ξ / r)‖
  have hmass' : (1 / 8 : ℝ) * R ≤ ∑ ξ ∈ S, w ξ := by
    simp only [euclideanCharacter_reciprocal] at hmass
    change (Finset.Icc L U).card / (4 : ℝ) ≤ ∑ ξ ∈ S, w ξ at hmass
    linarith
  have hcount' : (S.card : ℝ) ≤ D * (Real.log Q + 1) ^ d * Q := by
    have hs : (S.card : ℝ) ≤ (dualBall Λ (detectionTemperature d Q)).card := by
      exact_mod_cast (show S.card ≤ (dualBall Λ (detectionTemperature d Q)).card from Finset.card_erase_le)
    change _ ≤ D * Q * (Real.log Q + 1) ^ d at hcount
    nlinarith only [hs.trans hcount]
  let b : ℝ := R * Q ^ (-(11 / 10 : ℝ))
  let T := S.filter fun ξ => b ≤ w ξ
  have hb : 0 < b := by dsimp [b]; positivity
  have hmassT : R / 16 ≤ ∑ ξ ∈ T, w ξ := by
    have h := hremove Q hq₂ (euclideanDualLattice Λ) S w R hR0.le hcount' hmass'
    change (1 / 8 : ℝ) * R / 2 ≤ ∑ ξ ∈ T, w ξ at h
    linarith only [h]
  have hmem (ξ : euclideanDualLattice Λ) (hξ : ξ ∈ T) :
      ξ ≠ 0 ∧ ‖(ξ : E)‖ ≤ B * (Real.log Q + 1) := by
    have h := Finset.mem_erase.mp (Finset.mem_filter.mp hξ).1
    exact ⟨h.1, (mem_dualBall Λ _ ξ).mp h.2⟩
  have hz (ξ : euclideanDualLattice Λ) (hξ : ξ ∈ T) : |z ξ| ≤ A * R ^ 2 / w ξ := by
    have hn := (hmem ξ hξ).2
    have hnum : |z ξ| ≤ B * (Real.log R + 1) ^ 1 * R ^ (K + 1) := by
      calc
        _ ≤ ‖(ξ : E)‖ * ‖y‖ := abs_real_inner_le_norm _ _
        _ ≤ (B * (Real.log Q + 1)) * R ^ (K + 1) :=
          mul_le_mul hn hy (norm_nonneg _) (by positivity)
        _ ≤ B * (Real.log R + 1) ^ 1 * R ^ (K + 1) := by
          rw [pow_one]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hB.le) (by positivity)
    exact hsum R hr₁ Q (z ξ) (w ξ) L U hQ0 hQR hnum hL hU
      (Finset.mem_filter.mp hξ).2 le_rfl
  obtain ⟨m, hm, hmcover, hmlog⟩ := exists_dyadic_length Q hQ1
  have hupper (ξ : euclideanDualLattice Λ) (_ : ξ ∈ T) : w ξ < b * 2 ^ m := by
    have hw : w ξ ≤ 2 * R := (reciprocal_sum_le_card (z ξ) L U).trans hcardhi
    have hp : Q ^ (-(11 / 10 : ℝ)) * Q ^ (11 / 10 : ℝ) = 1 := by
      rw [← Real.rpow_add hQ0]; norm_num
    have h := mul_lt_mul_of_pos_left hmcover hb
    have he : b * (2 * Q ^ (11 / 10 : ℝ)) = 2 * R := by
      calc
        _ = 2 * R * (Q ^ (-(11 / 10 : ℝ)) * Q ^ (11 / 10 : ℝ)) := by dsimp [b]; ring
        _ = _ := by rw [hp, mul_one]
    rw [he] at h
    exact hw.trans_lt h
  have hbudget : 8 * (A * R ^ 2) * m / (R / 16) ≤ C * R * (Real.log Q + 1) := by
    have he : 8 * (A * R ^ 2) * m / (R / 16) = 128 * A * R * m := by field_simp; ring
    rw [he]
    have h := mul_le_mul_of_nonneg_left hmlog (show 0 ≤ 128 * A * R by positivity)
    have hp : 0 ≤ 2 * B * R * (Real.log Q + 1) := by positivity
    dsimp [C, M] at *
    nlinarith only [h, hp]
  have hnorm : 2 * B * (Real.log Q + 1) ≤ C * (Real.log Q + 1) := by
    have hp : 0 ≤ 128 * A * M * (Real.log Q + 1) := by positivity
    dsimp [C]; nlinarith only [hp]
  rcases dyadic_small_value_or_difference T w z b (R / 16) (A * R ^ 2) m hb
    (by positivity) (by positivity) hm (fun ξ hξ => (Finset.mem_filter.mp hξ).2)
    hupper hmassT hz with hsingle | hpair
  · obtain ⟨ξ, hξ, hsmall⟩ := hsingle
    obtain ⟨hne, hn⟩ := hmem ξ hξ
    refine ⟨ξ, ξ.property, (fun he => hne (Subtype.ext he)), ?_, hsmall.trans hbudget⟩
    calc
      _ ≤ B * (Real.log Q + 1) := hn
      _ ≤ 2 * B * (Real.log Q + 1) := by nlinarith [mul_nonneg hB.le (show 0 ≤ Real.log Q + 1 by linarith)]
      _ ≤ _ := hnorm
  · obtain ⟨ξ, hξ, η, hη, hne, hsmall⟩ := hpair
    refine ⟨(ξ : E) - η, (euclideanDualLattice Λ).sub_mem ξ.property η.property, ?_, ?_, ?_⟩
    · intro he
      exact hne (Subtype.ext (sub_eq_zero.mp he))
    · calc
        _ ≤ ‖(ξ : E)‖ + ‖(η : E)‖ := norm_sub_le _ _
        _ ≤ 2 * B * (Real.log Q + 1) := by linarith [(hmem ξ hξ).2, (hmem η hη).2]
        _ ≤ _ := hnorm
    · rw [inner_sub_left]
      exact hsmall.trans hbudget

end BakerHarman
