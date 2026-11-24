import UnforcedLeray.Units.B0583.TestModes

/-!
# B0583 helper: the gradient of the nonzero-mode velocity (order-zero multipliers)

Blueprint unit **B0583** (`prepared:p1.4`), `paper/main.tex` lines 9425–9426: "The gradient is
bounded by the Fourier multiplier of order zero."

For the nonzero-mode Biot–Savart velocity `K_c ω_ne = velNe c ω` of `B0581` (mode `k ≠ 0`:
`û_k = bsSymbol c k · ω̂_k`), the two partial derivatives act mode by mode as the multipliers

* `∂_q`: `iκ_k · bsSymbol c k` (`qModeCLM`, `κ_k = 2πk/c`), of modulus `≤ 1` since
  `|bsSymbol c k| ≤ |κ_k|⁻¹` (`norm_bsModeCLM_apply_le_kappa`);
* `∂_η`: `etaSymbol c k ξ = 2πiξ · bsSymbol c k ξ` (`etaModeCLM`), of modulus `≤ 1`
  (`B0581.norm_smul_bsSym_le`).

`gradQ c ω` and `gradEta c ω` are the resulting fields, with `‖gradQ c ω‖₂, ‖gradEta c ω‖₂ ≤ ‖ω‖₂`
(`norm_gradQ_le`, `norm_gradEta_le`). The identities `inner_pd0_velNe` and `inner_pd1_velNe`
show that they are the distributional derivatives of `velNe c ω` on the cylinder: for every
cylinder test function `φ` and `j ∈ {0, 1}`,
`⟪∂_q φ e_j, K_c ω_ne⟫ = -⟪φ e_j, gradQ c ω⟫` and `⟪∂_η φ e_j, K_c ω_ne⟫ = -⟪φ e_j, gradEta c ω⟫`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Complex Topology FourierTransform
open scoped ENNReal NNReal InnerProductSpace Real ComplexConjugate

namespace UnforcedLeray.B0583

open B0581

section Multipliers

variable (c : ℝ) [hc : Fact (0 < c)]

/-- The sharp nonzero-mode bound `‖𝓕⁻¹(bsSymbol c k · 𝓕 g)‖ ≤ |κ_k|⁻¹ ‖g‖`. -/
theorem norm_bsModeCLM_apply_le_kappa {k : ℤ} (hk : k ≠ 0) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖bsModeCLM c k g‖ ≤ |kappa c k|⁻¹ * ‖g‖ := by
  simp only [bsModeCLM, dif_neg hk, ContinuousLinearMap.comp_apply, fourierInvL2,
    fourierL2, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.norm_map]
  calc ‖symMulCLM (bsSymbol c k) (continuous_bsSymbol hc.out hk) (c / (2 * π))
        (norm_bsSymbol_le' hc.out hk) ((Lp.fourierTransformₗᵢ ℝ ℂ) g)‖
      ≤ |kappa c k|⁻¹ * ‖(Lp.fourierTransformₗᵢ ℝ ℂ) g‖ := by
        refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
        filter_upwards [coeFn_symMulCLM (bsSymbol c k) (continuous_bsSymbol hc.out hk)
          (c / (2 * π)) (norm_bsSymbol_le' hc.out hk) ((Lp.fourierTransformₗᵢ ℝ ℂ) g)]
          with ξ h
        rw [h, norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_right (norm_bsSymbol_le hc.out hk ξ).1 (norm_nonneg _)
    _ = |kappa c k|⁻¹ * ‖g‖ := by rw [LinearIsometryEquiv.norm_map]

/-- The mode-`k` multiplier of `∂_q K_c`: `iκ_k · bsModeCLM c k` (`0` for `k = 0`). -/
def qModeCLM (k : ℤ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp Vel 2 (volume : Measure ℝ) :=
  (I * (kappa c k : ℂ)) • bsModeCLM c k

theorem qModeCLM_apply (k : ℤ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    qModeCLM c k g = (I * (kappa c k : ℂ)) • bsModeCLM c k g := rfl

/-- Order zero: `‖∂_q` of the velocity mode`‖ ≤ ‖ω_k‖`. -/
theorem norm_qModeCLM_apply_le (k : ℤ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖qModeCLM c k g‖ ≤ 1 * ‖g‖ := by
  rw [qModeCLM_apply, norm_smul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  by_cases hk : k = 0
  · subst hk
    rw [bsModeCLM_zero, ContinuousLinearMap.zero_apply, norm_zero, mul_zero, one_mul]
    exact norm_nonneg _
  · have hκ : 0 < |kappa c k| := abs_pos.mpr (kappa_ne_zero hc.out hk)
    calc |kappa c k| * ‖bsModeCLM c k g‖ ≤ |kappa c k| * (|kappa c k|⁻¹ * ‖g‖) :=
          mul_le_mul_of_nonneg_left (norm_bsModeCLM_apply_le_kappa c hk g) hκ.le
      _ = 1 * ‖g‖ := by field_simp

/-- The mode-`k` symbol of `∂_η K_c` at Mathlib frequency `ξ`: `2πiξ · bsSymbol c k ξ`. -/
def etaSymbol (k : ℤ) (ξ : ℝ) : Vel := (((2 * π * ξ : ℝ) : ℂ) * I) • bsSymbol c k ξ

theorem norm_etaSymbol_le {k : ℤ} (hk : k ≠ 0) (ξ : ℝ) : ‖etaSymbol c k ξ‖ ≤ 1 := by
  have hκ := kappa_ne_zero hc.out hk
  have h : kappa c k ^ 2 + (2 * π * ξ) ^ 2 ≠ 0 := by positivity
  have := (norm_smul_bsSym_le h).2
  rw [etaSymbol, norm_smul, norm_mul, Complex.norm_I, mul_one, ← norm_smul]
  exact this

theorem continuous_etaSymbol {k : ℤ} (hk : k ≠ 0) : Continuous (etaSymbol c k) :=
  ((continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const).smul
    (continuous_bsSymbol hc.out hk)

/-- The mode-`k` multiplier of `∂_η K_c`: `g ↦ 𝓕⁻¹(etaSymbol c k · 𝓕 g)` (`0` for `k = 0`). -/
def etaModeCLM (k : ℤ) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp Vel 2 (volume : Measure ℝ) :=
  if hk : k = 0 then 0 else
    fourierInvL2 Vel ∘L
      symMulCLM (etaSymbol c k) (continuous_etaSymbol c hk) 1 (norm_etaSymbol_le c hk) ∘L
        fourierL2 ℂ

theorem etaModeCLM_zero : etaModeCLM c 0 = 0 := by simp [etaModeCLM]

theorem fourier_etaModeCLM {k : ℤ} (hk : k ≠ 0) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ((𝓕 (etaModeCLM c k g) : Lp Vel 2 (volume : Measure ℝ)) : ℝ → Vel) =ᵐ[volume]
      fun ξ => ((𝓕 g : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ • etaSymbol c k ξ := by
  have h : (𝓕 (etaModeCLM c k g) : Lp Vel 2 (volume : Measure ℝ)) =
      symMulCLM (etaSymbol c k) (continuous_etaSymbol c hk) 1 (norm_etaSymbol_le c hk) (𝓕 g) := by
    simp only [etaModeCLM, dif_neg hk, ContinuousLinearMap.comp_apply, fourierInvL2_apply,
      fourierL2_apply]
    exact FourierTransform.fourier_fourierInv_eq _
  rw [h]
  exact coeFn_symMulCLM _ _ _ _ _

theorem norm_etaModeCLM_apply_le (k : ℤ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖etaModeCLM c k g‖ ≤ 1 * ‖g‖ := by
  by_cases hk : k = 0
  · subst hk
    rw [etaModeCLM_zero, ContinuousLinearMap.zero_apply, norm_zero, one_mul]
    exact norm_nonneg _
  · simp only [etaModeCLM, dif_neg hk, ContinuousLinearMap.comp_apply, fourierInvL2,
      fourierL2, LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.norm_map]
    calc ‖symMulCLM (etaSymbol c k) (continuous_etaSymbol c hk) 1 (norm_etaSymbol_le c hk)
          ((Lp.fourierTransformₗᵢ ℝ ℂ) g)‖
        ≤ 1 * ‖(Lp.fourierTransformₗᵢ ℝ ℂ) g‖ := by
          refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
          filter_upwards [coeFn_symMulCLM (etaSymbol c k) (continuous_etaSymbol c hk) 1
            (norm_etaSymbol_le c hk) ((Lp.fourierTransformₗᵢ ℝ ℂ) g)] with ξ h
          rw [h, norm_smul, mul_comm]
          exact mul_le_mul_of_nonneg_right (norm_etaSymbol_le c hk ξ) (norm_nonneg _)
      _ = 1 * ‖g‖ := by rw [LinearIsometryEquiv.norm_map]

/-- The mode-wise multiplier of `∂_q K_c`. -/
def qModes : ModeSeq ℂ →L[ℂ] ModeSeq Vel :=
  diagCLM (qModeCLM c) 1 zero_le_one (norm_qModeCLM_apply_le c)

/-- The mode-wise multiplier of `∂_η K_c`. -/
def etaModes : ModeSeq ℂ →L[ℂ] ModeSeq Vel :=
  diagCLM (etaModeCLM c) 1 zero_le_one (norm_etaModeCLM_apply_le c)

/-- **`∂_q K_c ω_ne`**, as a field on the cell. -/
def gradQ : Lp ℂ 2 (cellVol c) →L[ℂ] Lp Vel 2 (cellVol c) :=
  (synth (F := Vel) c).toContinuousLinearMap ∘L qModes c ∘L modes (F := ℂ) c

/-- **`∂_η K_c ω_ne`**, as a field on the cell. -/
def gradEta : Lp ℂ 2 (cellVol c) →L[ℂ] Lp Vel 2 (cellVol c) :=
  (synth (F := Vel) c).toContinuousLinearMap ∘L etaModes c ∘L modes (F := ℂ) c

theorem gradQ_apply (ω : Lp ℂ 2 (cellVol c)) : gradQ c ω = synth c (qModes c (modes c ω)) := rfl

theorem gradEta_apply (ω : Lp ℂ 2 (cellVol c)) :
    gradEta c ω = synth c (etaModes c (modes c ω)) := rfl

/-- Order zero: `‖∂_q K_c ω_ne‖₂ ≤ ‖ω‖₂`. -/
theorem norm_gradQ_le (ω : Lp ℂ 2 (cellVol c)) : ‖gradQ c ω‖ ≤ ‖ω‖ := by
  rw [gradQ_apply, LinearIsometry.norm_map]
  calc ‖qModes c (modes c ω)‖ ≤ 1 * ‖modes c ω‖ := norm_diagCLM_apply_le _ _ _ _ _
    _ ≤ ‖ω‖ := by rw [one_mul]; exact norm_modes_le c ω

/-- Order zero: `‖∂_η K_c ω_ne‖₂ ≤ ‖ω‖₂`. -/
theorem norm_gradEta_le (ω : Lp ℂ 2 (cellVol c)) : ‖gradEta c ω‖ ≤ ‖ω‖ := by
  rw [gradEta_apply, LinearIsometry.norm_map]
  calc ‖etaModes c (modes c ω)‖ ≤ 1 * ‖modes c ω‖ := norm_diagCLM_apply_le _ _ _ _ _
    _ ≤ ‖ω‖ := by rw [one_mul]; exact norm_modes_le c ω

end Multipliers

/-! ### The weak-derivative identities -/

section Weak

variable (c : ℝ) [hc : Fact (0 < c)]

theorem inner_synth_right (T : Lp Vel 2 (cellVol c)) (g : ModeSeq Vel) :
    ⟪T, synth c g⟫_ℂ = ⟪modes c T, g⟫_ℂ := by
  rw [← inner_conj_symm, ← inner_modes, inner_conj_symm]

/-- `⟪∂_q φ e_j, K_c ω_ne⟫ = -⟪φ e_j, ∂_q K_c ω_ne⟫` for every cylinder test function `φ`. -/
theorem inner_pd0_velNe {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (j : Fin 2)
    (ω : Lp ℂ 2 (cellVol c)) :
    ⟪testLp c (hφ.pd 0) j, velNe c ω⟫_ℂ = -⟪testLp c hφ j, gradQ c ω⟫_ℂ := by
  rw [velNe_apply, gradQ_apply, inner_synth_right, inner_synth_right, lp.inner_eq_tsum,
    lp.inner_eq_tsum, ← tsum_neg]
  refine tsum_congr fun k => ?_
  rw [velModes_apply]
  change ⟪(modes c (testLp c (hφ.pd 0) j) : ModeSeq Vel) k, bsModeCLM c k _⟫_ℂ =
    -⟪(modes c (testLp c hφ j) : ModeSeq Vel) k, qModeCLM c k _⟫_ℂ
  rw [modes_testLp_pd0 c k hφ j, inner_smul_left, qModeCLM_apply, inner_smul_right]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `⟪∂_η φ e_j, K_c ω_ne⟫ = -⟪φ e_j, ∂_η K_c ω_ne⟫` for every cylinder test function `φ`. -/
theorem inner_pd1_velNe {φ : B0579.Plane → ℝ} (hφ : B0579.IsCylTest c φ) (j : Fin 2)
    (ω : Lp ℂ 2 (cellVol c)) :
    ⟪testLp c (hφ.pd 1) j, velNe c ω⟫_ℂ = -⟪testLp c hφ j, gradEta c ω⟫_ℂ := by
  rw [velNe_apply, gradEta_apply, inner_synth_right, inner_synth_right, lp.inner_eq_tsum,
    lp.inner_eq_tsum, ← tsum_neg]
  refine tsum_congr fun k => ?_
  rw [velModes_apply]
  change ⟪(modes c (testLp c (hφ.pd 1) j) : ModeSeq Vel) k, bsModeCLM c k _⟫_ℂ =
    -⟪(modes c (testLp c hφ j) : ModeSeq Vel) k, etaModeCLM c k _⟫_ℂ
  by_cases hk : k = 0
  · subst hk
    simp only [bsModeCLM_zero, etaModeCLM_zero, ContinuousLinearMap.zero_apply,
      inner_zero_right, neg_zero]
  · rw [← Lp.inner_fourier_eq, ← Lp.inner_fourier_eq (modes c (testLp c hφ j) k), L2.inner_def,
      L2.inner_def, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [fourier_modes_testLp_pd1 c k hφ j, fourier_bsModeCLM c hk
      ((modes c ω : ModeSeq ℂ) k), fourier_etaModeCLM c hk ((modes c ω : ModeSeq ℂ) k)]
      with ξ h1 h2 h3
    rw [h1, h2, h3, etaSymbol, inner_smul_left, inner_smul_right, inner_smul_right,
      inner_smul_right]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring

end Weak

end UnforcedLeray.B0583
