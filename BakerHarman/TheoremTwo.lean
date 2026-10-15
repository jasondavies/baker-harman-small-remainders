import BakerHarman.OriginalTheorem

/-!
# Baker–Harman's Theorem 2: shorter moduli for large weighted vectors

The diagonal lattice has minimum nonzero length at least the reciprocal of the
largest tolerance. Retaining that factor in the sharp lattice theorem gives the
improved modulus bound from equation (1.13).
-/

namespace BakerHarman

/-- The maximum of a real vector in a positive dimension. -/
noncomputable def coordinateMax {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ f

lemma le_coordinateMax {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (i : Fin n) :
    f i ≤ coordinateMax hn f := Finset.le_sup' f (Finset.mem_univ i)

lemma coordinateMax_le {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (b : ℝ)
    (h : ∀ i, f i ≤ b) : coordinateMax hn f ≤ b :=
  Finset.sup'_le _ _ (fun i _ => h i)

/-- The large weighted-vector case with `log Q + 1`. Only `ψᵢ ≤ 1` is needed
here; the stronger logarithmic weight restriction enters the paper's wrapper. -/
theorem bakerHarman_large_weighted_vector (n : ℕ) (hn : 0 < n) (K : ℝ) (hK : 1 ≤ K) :
    ∃ A B Q₀ R₀ : ℝ, 0 < A ∧ 0 < B ∧ 1 ≤ Q₀ ∧ 2 ≤ R₀ ∧
      ∀ Q R : ℝ, Q₀ ≤ Q → R₀ ≤ R → Q ≤ R ^ gammaBH K →
      ∀ a ψ : Fin n → ℝ, Real.sqrt (∑ i, (a i) ^ 2) ≤ R ^ K →
      (∀ i, 0 < ψ i) → (∀ i, ψ i ≤ 1) → (∏ i, ψ i) = Q⁻¹ →
      A * R * Q * (Real.log Q + 1) ^ n ≤ coordinateMax hn (fun i => |a i| / ψ i) →
      ∃ r : ℕ, R ≤ r ∧
        (r : ℝ) ≤ B * R * Q * (Real.log Q + 1) ^ (n - 1) * coordinateMax hn ψ ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, hlattice⟩ :=
    bakerHarman_sharp_lattice_approximation n hn K hK (gammaBH K)
      (gammaBH_pos K) (gammaBH_lt_analyticPowerRange K)
  refine ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, ?_⟩
  intro Q R hQ hR hQR a ψ ha hψ hψ1 hprod hlarge
  have hQ1 : 1 ≤ Q := hQ₀.trans hQ
  have hQ0 : 0 < Q := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  let E := EuclideanSpace ℝ (Fin n)
  let x : E := WithLp.toLp 2 a
  let y : E := WithLp.toLp 2 (fun i => a i / ψ i)
  let M := coordinateMax hn ψ
  have hM0 : 0 < M := (hψ ⟨0, hn⟩).trans_le (le_coordinateMax hn ψ _)
  have hM1 : M ≤ 1 := coordinateMax_le hn ψ 1 hψ1
  let ρ := M⁻¹
  have hρ1 : 1 ≤ ρ := (one_le_inv₀ hM0).mpr hM1
  let Λ := weightedCoordinateLattice ψ hψ
  have hsep : ∀ v ∈ Λ, v ≠ 0 → ρ ≤ ‖v‖ := by
    apply weightedCoordinateLattice_separation ψ hψ ρ (by dsimp [ρ]; positivity)
    intro i
    calc
      ρ * ψ i ≤ ρ * M := mul_le_mul_of_nonneg_left (le_coordinateMax hn ψ i)
        (by dsimp [ρ]; positivity)
      _ = 1 := inv_mul_cancel₀ hM0.ne'
  have hcov : ZLattice.covolume Λ = Q := by
    rw [weightedCoordinateLattice_covolume, hprod, inv_inv]
  have hx : ‖x‖ ≤ R ^ K := by
    have he : ‖x‖ = Real.sqrt (∑ i, (a i) ^ 2) := by
      simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_eq x
    rwa [he]
  have hQR' : Q ≤ R := hQR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR1
      (show gammaBH K ≤ 1 by linarith [gammaBH_le K]))
  have hyupper : ‖y‖ ≤ R ^ (K + 1) := by
    calc
      ‖y‖ ≤ Q * ‖x‖ := weighted_norm_le a ψ hψ Q hQ0.le
        (weighted_reciprocal_le Q hQ0 ψ hψ hψ1 hprod)
      _ ≤ R * R ^ K := mul_le_mul hQR' hx (norm_nonneg _) hR0.le
      _ = _ := by rw [Real.rpow_add hR0, Real.rpow_one]; ring
  have hmax : coordinateMax hn (fun i => |a i| / ψ i) ≤ ‖y‖ := by
    apply coordinateMax_le
    intro i
    have hh := PiLp.norm_apply_le y i
    change |a i / ψ i| ≤ ‖y‖ at hh
    rwa [abs_div, abs_of_pos (hψ i)] at hh
  obtain ⟨r, hr, hrupper, v, hv⟩ := hlattice R hR Q hQ hQR E
    finrank_euclideanSpace_fin Λ ρ hρ1 hsep hcov.le y
    (by simpa only [Nat.sub_add_cancel hn] using hlarge.trans hmax) hyupper
  have hrnonneg : (0 : ℤ) ≤ r := by exact_mod_cast (hR0.le.trans hr)
  have her : (r.toNat : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hrnonneg
  refine ⟨r.toNat, by simpa only [her] using hr, ?_, ?_⟩
  · simpa only [her, ρ, M, div_inv_eq_mul] using hrupper
  · have hh := weightedCoordinateLattice_reciprocal_approximation ψ hψ r a ⟨v, hv⟩
    simpa only [her] using hh

/-- Theorem 2 with the paper's logarithmic hypotheses and the stronger
shifted-sets exponent. The same `C₂` controls the tolerance bound and the large
weighted-vector threshold. Real `Q,R` are allowed. -/
theorem bakerHarman_theorem_two_log (n : ℕ) (hn : 0 < n) (K : ℝ) :
    ∃ C₁ C₂ C₃ : ℝ, 1 ≤ C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ Q R : ℝ, 1 ≤ R → C₁ ≤ Q → Q ≤ R ^ gammaBH K →
      ∀ a ψ : Fin n → ℝ, Real.sqrt (∑ i, (a i) ^ 2) ≤ R ^ K →
      (∀ i, 0 < ψ i) → (∀ i, ψ i ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n) →
      (∏ i, ψ i) = Q⁻¹ →
      C₂ * R * Q * (Real.log Q) ^ n ≤ coordinateMax hn (fun i => |a i| / ψ i) →
      ∃ r : ℕ, R ≤ r ∧
        (r : ℝ) ≤ C₃ * R * Q * (Real.log Q) ^ (n - 1) * coordinateMax hn ψ ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩ :=
    bakerHarman_large_weighted_vector n hn (max 1 K) (le_max_left _ _)
  let C₂ := max 1 (A * (2 : ℝ) ^ n)
  have hC₂1 : 1 ≤ C₂ := le_max_left _ _
  have hC₂ : 0 < C₂ := by linarith
  refine ⟨max Q₀ (max R₀ (Real.exp 1)), C₂, B * (2 : ℝ) ^ (n - 1),
    hQ₀.trans (le_max_left _ _), hC₂, by positivity, ?_⟩
  intro Q R hR hQ hQR a ψ ha hψ hψupper hprod hlarge
  have hR0 : 0 < R := by linarith
  have hQ₀Q : Q₀ ≤ Q := (le_max_left _ _).trans hQ
  have hQ1 : 1 ≤ Q := hQ₀.trans hQ₀Q
  have hQ0 : 0 < Q := by linarith
  have hR₀Q : R₀ ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans hQ)
  have hexpQ : Real.exp 1 ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans hQ)
  have hQleR : Q ≤ R := hQR.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR
      (show gammaBH K ≤ 1 by linarith [gammaBH_le K]))
  have hlog : 1 ≤ Real.log Q := by
    have hh := Real.log_le_log (Real.exp_pos 1) hexpQ
    simpa only [Real.log_exp] using hh
  have hlog0 : 0 < Real.log Q := by linarith
  have hψ1 (i) : ψ i ≤ 1 := by
    have hci : C₂⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC₂1
    have hli : (Real.log Q)⁻¹ ^ n ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr hlog0.le) (inv_le_one_of_one_le₀ hlog)
    calc
      ψ i ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n := hψupper i
      _ ≤ 1 * 1 := mul_le_mul hci hli (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hpow (m : ℕ) : (Real.log Q + 1) ^ m ≤ (2 : ℝ) ^ m * (Real.log Q) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hlower : A * R * Q * (Real.log Q + 1) ^ n ≤
      coordinateMax hn (fun i => |a i| / ψ i) := by
    apply le_trans _ hlarge
    have hh := mul_le_mul_of_nonneg_left (hpow n) (show 0 ≤ A * R * Q by positivity)
    have hc := mul_le_mul_of_nonneg_right (le_max_right 1 (A * (2 : ℝ) ^ n))
      (show 0 ≤ R * Q * (Real.log Q) ^ n by positivity)
    nlinarith only [hh, hc]
  have hγ : gammaBH (max 1 K) = gammaBH K := by simp [gammaBH]
  obtain ⟨r, hr, hrupper, herr⟩ := h Q R hQ₀Q (hR₀Q.trans hQleR) (by rwa [hγ]) a ψ
    (ha.trans (Real.rpow_le_rpow_of_exponent_le hR (le_max_right _ _)))
    hψ hψ1 hprod hlower
  refine ⟨r, hr, hrupper.trans ?_, herr⟩
  have hM : 0 ≤ coordinateMax hn ψ :=
    (hψ ⟨0, hn⟩).le.trans (le_coordinateMax hn ψ _)
  have hh := mul_le_mul_of_nonneg_left (hpow (n - 1))
    (show 0 ≤ B * R * Q * coordinateMax hn ψ by positivity)
  nlinarith only [hh]

/-- **Baker–Harman, Theorem 2** (1996), equations (1.12)–(1.13), with
its original power exponent. All constants depend only on the dimension and
`K`; arbitrary real coordinate signs and dimension one are included. -/
theorem bakerHarman_theorem_two (n : ℕ) (hn : 0 < n) (K : ℝ) (_hK : 0 < K) :
    ∃ C₁ C₂ C₃ : ℝ, 1 ≤ C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ Q R : ℕ, C₁ ≤ Q → (Q : ℝ) ≤ (R : ℝ) ^ originalExponent K →
      ∀ a ψ : Fin n → ℝ, Real.sqrt (∑ i, (a i) ^ 2) ≤ (R : ℝ) ^ K →
      (∀ i, 0 < ψ i) → (∀ i, ψ i ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n) →
      (∏ i, ψ i) = (Q : ℝ)⁻¹ →
      C₂ * R * Q * (Real.log Q) ^ n ≤ coordinateMax hn (fun i => |a i| / ψ i) →
      ∃ r : ℕ, R ≤ r ∧
        (r : ℝ) ≤ C₃ * R * Q * (Real.log Q) ^ (n - 1) * coordinateMax hn ψ ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h⟩ := bakerHarman_theorem_two_log n hn K
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro Q R hQ hQR a ψ ha hψ hψupper hprod hlarge
  have hRpos : 0 < R := by
    by_contra hR
    have he : R = 0 := by omega
    rw [he, Nat.cast_zero, Real.zero_rpow (originalExponent_pos K).ne'] at hQR
    linarith
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hRpos
  have hQR' : (Q : ℝ) ≤ (R : ℝ) ^ gammaBH K := hQR.trans
    (Real.rpow_le_rpow_of_exponent_le hR1 (originalExponent_le_gammaBH K))
  obtain ⟨r, hr, hrupper, herr⟩ := h Q R hR1 hQ hQR' a ψ ha hψ hψupper hprod hlarge
  exact ⟨r, by exact_mod_cast hr, hrupper, herr⟩

end BakerHarman
