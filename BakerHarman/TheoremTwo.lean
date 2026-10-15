import BakerHarman.OriginalTheorem

/-!
# Baker–Harman's Theorem 2: shorter moduli for large weighted vectors

The diagonal lattice has minimum nonzero length at least the reciprocal of the
largest tolerance. Retaining that factor in the sharp lattice theorem gives the
improved modulus bound from equation (1.13).

The paper assumes `K > 0`, which the natural-parameter statement preserves.
`bakerHarman_theorem_two_constants` exports `exp 1 ≤ C₁` and `1 ≤ C₂`.
For these bounds, the hypotheses are incompatible when `K ≤ 1`:
`ψᵢ⁻¹ ≤ Q` bounds the weighted maximum by `R^K Q ≤ RQ`, while the required
lower bound is strictly above `RQ`. `BakerHarman.TheoremTwoRange` proves this
incompatibility and constructs admissible inputs for every `K > 1` and every
allowed pair of constants.
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
  obtain ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, h⟩ :=
    bakerHarman_weighted_lattice_approximation n hn K hK
  refine ⟨A, B, Q₀, R₀, hA, hB, hQ₀, hR₀, ?_⟩
  intro Q R hQ hR hQR a ψ ha hψ hψ1 hprod hlarge
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => a i / ψ i)
  let M := coordinateMax hn ψ
  have hM0 : 0 < M := (hψ ⟨0, hn⟩).trans_le (le_coordinateMax hn ψ _)
  have hM1 : M ≤ 1 := coordinateMax_le hn ψ 1 hψ1
  let ρ := M⁻¹
  have hρ1 : 1 ≤ ρ := (one_le_inv₀ hM0).mpr hM1
  have hρψ (i) : ρ * ψ i ≤ 1 := by
    calc
      ρ * ψ i ≤ ρ * M := mul_le_mul_of_nonneg_left (le_coordinateMax hn ψ i)
        (by dsimp [ρ]; positivity)
      _ = 1 := inv_mul_cancel₀ hM0.ne'
  have hmax : coordinateMax hn (fun i => |a i| / ψ i) ≤ ‖y‖ := by
    apply coordinateMax_le
    intro i
    have hh := PiLp.norm_apply_le y i
    change |a i / ψ i| ≤ ‖y‖ at hh
    rwa [abs_div, abs_of_pos (hψ i)] at hh
  obtain ⟨r, hr, hrupper, herr⟩ :=
    h Q R hQ hR hQR a ψ ha hψ hprod ρ hρ1 hρψ (hlarge.trans hmax)
  exact ⟨r, hr, by simpa only [ρ, M, div_inv_eq_mul] using hrupper, herr⟩

/-- Theorem 2 with the paper's logarithmic hypotheses and the stronger
shifted-sets exponent. The same `C₂` controls the tolerance bound and the large
weighted-vector threshold. Real `Q,R` are allowed. The constant bounds are
exported explicitly for the K-range lemmas. -/
theorem bakerHarman_theorem_two_log_constants (n : ℕ) (hn : 0 < n) (K : ℝ) :
    ∃ C₁ C₂ C₃ : ℝ, Real.exp 1 ≤ C₁ ∧ 1 ≤ C₂ ∧ 0 < C₃ ∧
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
  refine ⟨logarithmicThreshold Q₀ R₀, C₂, B * (2 : ℝ) ^ (n - 1),
    logarithmicThreshold_ge_exp Q₀ R₀, hC₂1, by positivity, ?_⟩
  intro Q R hR hQ hQR a ψ ha hψ hψupper hprod hlarge
  have hR0 : 0 < R := by linarith
  obtain ⟨hQ₀Q, hR₀R, hlog⟩ :=
    logarithmic_parameter_bounds (gammaBH K) Q₀ R₀ Q R (by linarith [gammaBH_le K]) hR hQ hQR
  have hQ1 : 1 ≤ Q := hQ₀.trans hQ₀Q
  have hQ0 : 0 < Q := by linarith
  have hlog0 : 0 < Real.log Q := by linarith
  have hψ1 (i) : ψ i ≤ 1 := by
    have hci : C₂⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC₂1
    have hli : (Real.log Q)⁻¹ ^ n ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr hlog0.le) (inv_le_one_of_one_le₀ hlog)
    calc
      ψ i ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n := hψupper i
      _ ≤ 1 * 1 := mul_le_mul hci hli (by positivity) (by norm_num)
      _ = 1 := by norm_num
  have hlower : A * R * Q * (Real.log Q + 1) ^ n ≤
      coordinateMax hn (fun i => |a i| / ψ i) := by
    apply le_trans _ hlarge
    have hh := mul_le_mul_of_nonneg_left (log_add_one_pow_le_two_mul_log_pow Q hlog n)
      (show 0 ≤ A * R * Q by positivity)
    have hc := mul_le_mul_of_nonneg_right (le_max_right 1 (A * (2 : ℝ) ^ n))
      (show 0 ≤ R * Q * (Real.log Q) ^ n by positivity)
    nlinarith only [hh, hc]
  have hγ : gammaBH (max 1 K) = gammaBH K := by simp [gammaBH]
  obtain ⟨r, hr, hrupper, herr⟩ := h Q R hQ₀Q hR₀R (by rwa [hγ]) a ψ
    (ha.trans (Real.rpow_le_rpow_of_exponent_le hR (le_max_right _ _)))
    hψ hψ1 hprod hlower
  refine ⟨r, hr, hrupper.trans ?_, herr⟩
  have hM : 0 ≤ coordinateMax hn ψ :=
    (hψ ⟨0, hn⟩).le.trans (le_coordinateMax hn ψ _)
  have hh := mul_le_mul_of_nonneg_left (log_add_one_pow_le_two_mul_log_pow Q hlog (n - 1))
    (show 0 ≤ B * R * Q * coordinateMax hn ψ by positivity)
  nlinarith only [hh]

/-- The real-parameter Theorem 2 interface, retaining its original statement. -/
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
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h⟩ :=
    bakerHarman_theorem_two_log_constants n hn K
  exact ⟨C₁, C₂, C₃, (Real.one_le_exp (by norm_num)).trans hC₁,
    lt_of_lt_of_le zero_lt_one hC₂, hC₃, h⟩

/-- **Baker–Harman, Theorem 2** (1996), equations (1.12)–(1.13), with
its original power exponent. All constants depend only on the dimension and
`K`; arbitrary real coordinate signs and dimension one are included.
The `0 < K` argument matches the paper; for the constants constructed here, the
hypotheses can only hold when `K > 1` (see the module documentation). -/
theorem bakerHarman_theorem_two_constants (n : ℕ) (hn : 0 < n) (K : ℝ) (_hK : 0 < K) :
    ∃ C₁ C₂ C₃ : ℝ, Real.exp 1 ≤ C₁ ∧ 1 ≤ C₂ ∧ 0 < C₃ ∧
      ∀ Q R : ℕ, C₁ ≤ Q → (Q : ℝ) ≤ (R : ℝ) ^ originalExponent K →
      ∀ a ψ : Fin n → ℝ, Real.sqrt (∑ i, (a i) ^ 2) ≤ (R : ℝ) ^ K →
      (∀ i, 0 < ψ i) → (∀ i, ψ i ≤ C₂⁻¹ * (Real.log Q)⁻¹ ^ n) →
      (∏ i, ψ i) = (Q : ℝ)⁻¹ →
      C₂ * R * Q * (Real.log Q) ^ n ≤ coordinateMax hn (fun i => |a i| / ψ i) →
      ∃ r : ℕ, R ≤ r ∧
        (r : ℝ) ≤ C₃ * R * Q * (Real.log Q) ^ (n - 1) * coordinateMax hn ψ ∧
        ∀ i, distNearestInt (a i / r) ≤ ψ i := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h⟩ := bakerHarman_theorem_two_log_constants n hn K
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro Q R hQ hQR a ψ ha hψ hψupper hprod hlarge
  obtain ⟨hR1, hQR'⟩ := originalExponent_nat_parameters K Q R
    ((Real.one_le_exp (by norm_num)).trans (hC₁.trans hQ)) hQR
  obtain ⟨r, hr, hrupper, herr⟩ := h Q R hR1 hQ hQR' a ψ ha hψ hψupper hprod hlarge
  exact ⟨r, by exact_mod_cast hr, hrupper, herr⟩

/-- The original paper-facing Theorem 2 interface. The stronger constant
bounds are available in `bakerHarman_theorem_two_constants`. Its `0 < K`
argument retains the paper's stated range. -/
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
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, h⟩ :=
    bakerHarman_theorem_two_constants n hn K _hK
  exact ⟨C₁, C₂, C₃, (Real.one_le_exp (by norm_num)).trans hC₁,
    lt_of_lt_of_le zero_lt_one hC₂, hC₃, h⟩

end BakerHarman
