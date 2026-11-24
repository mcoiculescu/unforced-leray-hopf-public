import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Part II-b, task `PartII-b:T16/2` (`TestedGradientEnergyH2`): decomposition and setup

Source of record: `the November 2 reference manuscript`, lines 1955-1985.

Upgrades the enlarged-box `H_2` bound `ω` on `w = b_ε - b_0` (`obsBox (σ/2) (2*H₁) (L₁+1)`) to the
localized gradient bound on `obsBox σ H₁ L₁`.

## Proved here (zero `sorry`)

1. **Uniqueness of weak first-order derivatives and `r = 2` graph bounds for given derivatives**:
   `hasWeakFO_unique_ae`, `hasWeakVec_unique_ae`, `phys_graph_poly_two_given`,
   `flat_graph_poly_two_given`, `exists_inHr_weakS_of_isResponse`.
2. **Weak `Q_ε` derivative of `b_0` (`qepsOf`) and `Q_ε w` vs `Qb_ε - Qb_0` splitting**:
   `qepsOf`, `hasWeakFO_qepsOf`, `hasWeakVec_qepsOf`, `indBox_sqrtS_q_pointwise`,
   `hNorm_indBox_sqrtS_q_le_qw`.
3. **Smooth observation-box cutoff `boxCutoff σ H₁ L₁`**:
   `sBoxCut`, `etaBoxCut`, `boxCutoff`, `driftCutoff_boxCutoff`, `boxCutoff_nonneg`,
   `boxCutoff_le_one`, `boxCutoff_eq_one_of_mem`, `boxCutoff_eq_zero_of_notMem`,
   `hNorm_indBox_le_boxCutoff_smul`, `hNorm_boxCutoff_smul_le_enlarged`,
   `hNorm_boxCutoff_sq_smul_le_enlarged`.
4. **Weak product rule for `ψ • w` and `χ² • w`**:
   `vGrad`, `weakSmul`, `coordTranspose_mul_smooth`, `hasWeakFO_smul_smooth`,
   `hasWeakVec_smul_smooth`, `drift_identity_H2_given`.
5. **Combined chart-level tested energy inequality and conditional assembly**:
   `SubtractedChartTestedEq` (`PartII-b:T16/2/1`), `subtracted_chart_energy_ineq`
   (combining `SubtractedChartTestedEq`, `drift_identity_H2_given`, and
   `diffusion_difference_terms`), `BoxDiffusionAbsorption` (`PartII-b:T16/2/2`), and
   `testedGradientEnergyH2_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-! ## 1. Uniqueness of weak derivatives and `r = 2` graph bounds for given derivatives -/

/-- Any two weak `HasWeakFO v d` derivatives of the same function `u` agree `hMeas c r`-a.e. -/
theorem hasWeakFO_unique_ae {c r : ℝ} (hc : 0 < c) {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    {u g₁ g₂ : Coord → ℂ} (h₁ : HasWeakFO v d u g₁) (h₂ : HasWeakFO v d u g₂) :
    g₁ =ᵐ[hMeas c r] g₂ := by
  have hz : ∀ᵐ x ∂(Axi.ageμ c (r / 2 - 5 / 2)), (g₁ x - g₂ x) = 0 := by
    refine qd_ae_zero c (r / 2 - 5 / 2) hc (fun x => g₁ x - g₂ x) (fun φ hφ => ?_)
    have hpt : (fun x => (g₁ x - g₂ x) * (φ x : ℂ)) =
        fun x => g₁ x * (φ x : ℂ) - g₂ x * (φ x : ℂ) := by
      funext x; ring
    rw [hpt]
    refine ⟨(h₁.1 φ hφ).2.sub (h₂.1 φ hφ).2, ?_⟩
    rw [integral_sub (h₁.1 φ hφ).2 (h₂.1 φ hφ).2, h₁.2 φ hφ, h₂.2 φ hφ, sub_self]
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

/-- Any two weak `HasWeakVec v d` derivatives of the same profile `b` agree `hMeas c r`-a.e. -/
theorem hasWeakVec_unique_ae {c r : ℝ} (hc : 0 < c) {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    {b g₁ g₂ : CProf} (h₁ : HasWeakVec v d b g₁) (h₂ : HasWeakVec v d b g₂) :
    g₁ =ᵐ[hMeas c r] g₂ := by
  have h0 := hasWeakFO_unique_ae (r := r) hc (h₁ 0) (h₂ 0)
  have h1 := hasWeakFO_unique_ae (r := r) hc (h₁ 1) (h₂ 1)
  filter_upwards [h0, h1] with x hx0 hx1
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

theorem sqrtS_congr_ae {c r : ℝ} {g₁ g₂ : CProf} (h : g₁ =ᵐ[hMeas c r] g₂) :
    sqrtS g₁ =ᵐ[hMeas c r] sqrtS g₂ := by
  filter_upwards [h] with x hx
  simp [sqrtS, hx]

/-- `phys_graph_poly` at `r = 2` transferred to any given weak derivatives `Sbε, Qbε, Ebε`. -/
theorem phys_graph_poly_two_given :
    ∃ Cp : ℝ, 0 < Cp ∧
      ∀ (Γ ν c ε : ℝ) (μ : ℂ), 1 ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 4 →
        0 < ν → 0 < c → 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
      ∀ F bε Sbε Qbε Ebε : CProf, InHr c 2 F → IsResponse ν c ε μ 2 F bε →
        HasWeakVec vS dZero bε Sbε → HasWeakVec (vQ ε) (dQ ε) bε Qbε →
        HasWeakVec vEta dZero bε Ebε →
        hNorm c 2 bε + hNorm c 2 Sbε +
            ENNReal.ofReal (Real.sqrt ν) * (hNorm c 2 (sqrtS Qbε) + hNorm c 2 (sqrtS Ebε)) ≤
          ENNReal.ofReal (Cp * Γ ^ 2) * hNorm c 2 F := by
  obtain ⟨Cp, hCp, hphys⟩ := phys_graph_poly 2 (by norm_num) (by norm_num)
  have hgap2 : (3 / (2 : ℝ) - 1) / 2 = 1 / 4 := by norm_num
  refine ⟨Cp, hCp, ?_⟩
  intro Γ ν c ε μ hΓ1 hμΓ hgap hν hc hε0 hε1 hP F bε Sbε Qbε Ebε hF hbε_resp hS hQ hE
  have hgap' : Γ⁻¹ ≤ μ.re + (3 / (2 : ℝ) - 1) / 2 := by rwa [hgap2]
  obtain ⟨Sb', Qb', Eb', hS', hQ', hE', -, -, -, hg⟩ :=
    hphys Γ ν c ε μ hΓ1 hμΓ hgap' hν hc hε0 hε1 hP F bε hF hbε_resp
  have eS : hNorm c 2 Sbε = hNorm c 2 Sb' :=
    eLpNorm_congr_ae (hasWeakVec_unique_ae hc hS hS')
  have eQ : hNorm c 2 (sqrtS Qbε) = hNorm c 2 (sqrtS Qb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae (hasWeakVec_unique_ae hc hQ hQ'))
  have eE : hNorm c 2 (sqrtS Ebε) = hNorm c 2 (sqrtS Eb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae (hasWeakVec_unique_ae hc hE hE'))
  rwa [eS, eQ, eE]

/-- `flat_graph_poly` at `r = 2` transferred to any given weak derivatives `Sb0, Qb0, Eb0`. -/
theorem flat_graph_poly_two_given :
    ∃ Cf : ℝ, 0 < Cf ∧
      ∀ (Γ ν c : ℝ) (μ : ℂ), 1 ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 4 →
        0 < ν → 0 < c →
      ∀ F b0 Sb0 Qb0 Eb0 : CProf, InHr c 2 F → IsFlatResponse ν μ F b0 → InFlatClass c 2 b0 →
        HasWeakVec vS dZero b0 Sb0 → HasWeakVec vQ0 dZero b0 Qb0 →
        HasWeakVec vEta dZero b0 Eb0 →
        hNorm c 2 b0 + hNorm c 2 Sb0 +
            ENNReal.ofReal (Real.sqrt ν) * (hNorm c 2 (sqrtS Qb0) + hNorm c 2 (sqrtS Eb0)) ≤
          ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c 2 F := by
  obtain ⟨Cf, hCf, hflat⟩ := flat_graph_poly 2 (by norm_num) (by norm_num)
  have hgap2 : (3 / (2 : ℝ) - 1) / 2 = 1 / 4 := by norm_num
  refine ⟨Cf, hCf, ?_⟩
  intro Γ ν c μ hΓ1 hμΓ hgap hν hc F b0 Sb0 Qb0 Eb0 hF hb0_resp hb0_class hS hQ hE
  have hgap' : Γ⁻¹ ≤ μ.re + (3 / (2 : ℝ) - 1) / 2 := by rwa [hgap2]
  obtain ⟨Sb', Qb', Eb', hS', hQ', hE', -, -, -, hg⟩ :=
    hflat Γ ν c μ hΓ1 hμΓ hgap' hν hc F b0 hF hb0_resp hb0_class
  have eS : hNorm c 2 Sb0 = hNorm c 2 Sb' :=
    eLpNorm_congr_ae (hasWeakVec_unique_ae hc hS hS')
  have eQ : hNorm c 2 (sqrtS Qb0) = hNorm c 2 (sqrtS Qb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae (hasWeakVec_unique_ae hc hQ hQ'))
  have eE : hNorm c 2 (sqrtS Eb0) = hNorm c 2 (sqrtS Eb') :=
    eLpNorm_congr_ae (sqrtS_congr_ae (hasWeakVec_unique_ae hc hE hE'))
  rwa [eS, eQ, eE]

/-- Existence of an `InHr c 2` representative of the weak `S`-derivative of `bε`. -/
theorem exists_inHr_weakS_of_isResponse {ν c ε : ℝ} {μ : ℂ} (hc : 0 < c) (hε : 0 < ε)
    {F bε : CProf} (hbε : IsResponse ν c ε μ 2 F bε) :
    ∃ Sbε' : CProf, HasWeakVec vS dZero bε Sbε' ∧ InHr c 2 Sbε' := by
  have hP0 : 0 < 2 * ε * c := by positivity
  have hbY : IsInYr (2 * ε * c) 2 (NvC ε⁻¹ bε) := hbε.mem_w
  obtain ⟨b', hbb'p, -, hb'H, hNN⟩ := profileRegularize_proof c ε 2 bε hc hε two_pos hbY
  have hb'R : IsFreeResponse ν μ 2 (2 * ε * c) (NvC ε⁻¹ F) (NvC ε⁻¹ b') :=
    freeResponseCongr_proof ν μ 2 _ _ _ _ _ hP0 Filter.EventuallyEq.rfl hNN.symm hbε
  obtain ⟨d, hdY, hdp⟩ := hb'R.drift
  obtain ⟨Sb, hSb, hSbH, -⟩ := driftRecovery_proof c ε 2 b' d hc hε one_lt_two hb'H hdY hdp
  have hsym : ∀ᵐ x ∂posReg, bε x = b' x := hbb'p.mono fun x hx => hx.symm
  exact ⟨Sb, weakVecCongr_proof vS dZero b' bε Sb hsym hSb, hSbH⟩

/-! ## Section 2: `Q_ε` of the flat profile (`qepsOf`) and `Qbε - Qb0` vs `Qw` on `obsBox` -/

/-- Reconstruct the weak `Q_ε = ∂_q - ε(2S + η∂_η + 1)` derivative from `(∂_q, S, ∂_η)`. -/
def qepsOf (ε : ℝ) (b Sb Db Eb : CProf) : CProf :=
  fun x => WithLp.toLp 2 fun i =>
    Db x i - (ε : ℂ) * (2 * Sb x i + (x.2.2 : ℂ) * Eb x i + b x i)

@[simp]
theorem qepsOf_apply (ε : ℝ) (b Sb Db Eb : CProf) (x : Coord) (i : Fin 2) :
    qepsOf ε b Sb Db Eb x i =
      Db x i - (ε : ℂ) * (2 * Sb x i + (x.2.2 : ℂ) * Eb x i + b x i) := rfl

theorem qepsOf_eq_sub (ε : ℝ) (b Sb Db Eb : CProf) (x : Coord) :
    qepsOf ε b Sb Db Eb x =
      Db x - (ε : ℂ) • ((2 : ℂ) • Sb x + (x.2.2 : ℂ) • Eb x + b x) := by
  ext i
  simp [qepsOf]
  ring

/-- Scalar weak `Q_ε` derivative from `(S, ∂_q, ∂_η)`. -/
theorem hasWeakFO_qepsOf (ε : ℝ) {u Su Du Eu : Coord → ℂ}
    (hS : HasWeakFO vS dZero u Su)
    (hD : HasWeakFO vQ0 dZero u Du)
    (hE : HasWeakFO vEta dZero u Eu) :
    HasWeakFO (vQ ε) (dQ ε) u
      (fun x => Du x - (ε : ℂ) * (2 * Su x + (x.2.2 : ℂ) * Eu x + u x)) := by
  set Qu : Coord → ℂ := fun x => Du x - (ε : ℂ) * (2 * Su x + (x.2.2 : ℂ) * Eu x + u x)
  have h_int : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => u x * (coordTranspose (vQ ε) (dQ ε) φ x : ℂ)) ∧
        Integrable (fun x => Qu x * (φ x : ℂ)) := by
    intro φ hφ
    have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hη := qd_test_mul_snd hφ
    have huφ := integrable_mul_coordTest hE hφ
    have hID := (hD.1 φ hφ).1
    have hIS := (hS.1 φ hφ).1
    have hIE := (hE.1 _ hη).1
    have hFD := (hD.1 φ hφ).2
    have hFS := (hS.1 φ hφ).2
    have hFE := (hE.1 _ hη).2
    refine ⟨?_, ?_⟩
    · have hpt : ∀ x : Coord,
          u x * (coordTranspose (vQ ε) (dQ ε) φ x : ℂ) =
            u x * (coordTranspose vQ0 dZero φ x : ℂ) -
              (2 * (ε : ℂ)) * (u x * (coordTranspose vS dZero φ x : ℂ)) -
              (ε : ℂ) * (u x * (coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℂ)) -
              (ε : ℂ) * (u x * (φ x : ℂ)) := by
        intro x
        have hr := qd_real ε φ hφd x
        have hc : (ε : ℂ) * (φ x : ℂ) = -((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ) +
            ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ) -
            2 * (ε : ℂ) * ((coordTranspose vS dZero φ x : ℝ) : ℂ) -
            (ε : ℂ) * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ) := by
          exact_mod_cast hr
        linear_combination (u x) * hc
      exact (((hID.sub (hIS.const_mul (2 * (ε : ℂ)))).sub
        (hIE.const_mul (ε : ℂ))).sub (huφ.const_mul (ε : ℂ))).congr
          (ae_of_all _ fun x => (hpt x).symm)
    · have hpt : ∀ x : Coord,
          Qu x * (φ x : ℂ) =
            Du x * (φ x : ℂ) -
              (2 * (ε : ℂ)) * (Su x * (φ x : ℂ)) -
              (ε : ℂ) * (Eu x * ((x.2.2 * φ x : ℝ) : ℂ)) -
              (ε : ℂ) * (u x * (φ x : ℂ)) := by
        intro x
        dsimp [Qu]
        push_cast
        ring
      exact (((hFD.sub (hFS.const_mul (2 * (ε : ℂ)))).sub
        (hFE.const_mul (ε : ℂ))).sub (huφ.const_mul (ε : ℂ))).congr
          (ae_of_all _ fun x => (hpt x).symm)
  refine ⟨h_int, fun φ hφ => ?_⟩
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hη := qd_test_mul_snd hφ
  obtain ⟨hI0, hF1⟩ := h_int φ hφ
  have hID := (hD.1 φ hφ).1
  have hIS := (hS.1 φ hφ).1
  have hIE := (hE.1 _ hη).1
  have hF2 := (hD.1 φ hφ).2
  have hF3 := (hS.1 φ hφ).2
  have hF4 := (hE.1 _ hη).2
  have i2 : Integrable (fun x => Du x * (φ x : ℂ) -
      u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ)) := hF2.sub hID
  have i3 : Integrable (fun x => Su x * (φ x : ℂ) -
      u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ)) := hF3.sub hIS
  have i4 : Integrable (fun x => Eu x * ((x.2.2 * φ x : ℝ) : ℂ) -
      u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) := hF4.sub hIE
  have z2 : ∫ x, (Du x * (φ x : ℂ) -
      u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF2 hID, hD.2 φ hφ, sub_self]
  have z3 : ∫ x, (Su x * (φ x : ℂ) -
      u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF3 hIS, hS.2 φ hφ, sub_self]
  have z4 : ∫ x, (Eu x * ((x.2.2 * φ x : ℝ) : ℂ) -
      u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) = 0 := by
    rw [integral_sub hF4 hIE, hE.2 _ hη, sub_self]
  have hpt : ∀ x : Coord,
      Qu x * (φ x : ℂ) - u x * (coordTranspose (vQ ε) (dQ ε) φ x : ℂ) =
        ((Du x * (φ x : ℂ) - u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ)) -
          2 * (ε : ℂ) * (Su x * (φ x : ℂ) - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ))) -
          (ε : ℂ) * (Eu x * ((x.2.2 * φ x : ℝ) : ℂ) -
            u x * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ)) := by
    intro x
    have hr := qd_real ε φ hφd x
    have hc : (ε : ℂ) * (φ x : ℂ) = -((coordTranspose (vQ ε) (dQ ε) φ x : ℝ) : ℂ) +
        ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ) -
        2 * (ε : ℂ) * ((coordTranspose vS dZero φ x : ℝ) : ℂ) -
        (ε : ℂ) * ((coordTranspose vEta dZero (fun y => y.2.2 * φ y) x : ℝ) : ℂ) := by
      exact_mod_cast hr
    dsimp [Qu]
    push_cast
    linear_combination -(u x) * hc
  have i23 : Integrable (fun x => (Du x * (φ x : ℂ) -
      u x * ((coordTranspose vQ0 dZero φ x : ℝ) : ℂ)) -
      2 * (ε : ℂ) * (Su x * (φ x : ℂ) - u x * ((coordTranspose vS dZero φ x : ℝ) : ℂ))) :=
    i2.sub (i3.const_mul (2 * (ε : ℂ)))
  have hdiff : ∫ x, (Qu x * (φ x : ℂ) - u x * (coordTranspose (vQ ε) (dQ ε) φ x : ℂ)) = 0 := by
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_sub i23 (i4.const_mul (ε : ℂ)),
      integral_sub i2 (i3.const_mul (2 * (ε : ℂ))),
      integral_const_mul, integral_const_mul, z2, z3, z4]
    ring
  rw [← sub_eq_zero, ← integral_sub hF1 hI0]
  exact hdiff

/-- Vector weak `Q_ε` derivative from `(S, ∂_q, ∂_η)`. -/
theorem hasWeakVec_qepsOf (ε : ℝ) {b Sb Db Eb : CProf}
    (hS : HasWeakVec vS dZero b Sb)
    (hD : HasWeakVec vQ0 dZero b Db)
    (hE : HasWeakVec vEta dZero b Eb) :
    HasWeakVec (vQ ε) (dQ ε) b (qepsOf ε b Sb Db Eb) := by
  intro i
  exact hasWeakFO_qepsOf ε (hS i) (hD i) (hE i)

theorem aestronglyMeasurable_sqrtS_of {μ : Measure Coord} {u : CProf}
    (hu : AEStronglyMeasurable u μ) : AEStronglyMeasurable (sqrtS u) μ := by
  have hm : Measurable (fun x : Coord => (Real.sqrt x.1 : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_fst)
  exact hm.aestronglyMeasurable.smul hu

theorem aestronglyMeasurable_sqrtS_qepsOf {μ : Measure Coord} (ε : ℝ) {b Sb Db Eb : CProf}
    (mb : AEStronglyMeasurable b μ) (mS : AEStronglyMeasurable Sb μ)
    (mD : AEStronglyMeasurable (sqrtS Db) μ) (mE : AEStronglyMeasurable (sqrtS Eb) μ) :
    AEStronglyMeasurable (sqrtS (qepsOf ε b Sb Db Eb)) μ := by
  have hη : Measurable (fun x : Coord => (x.2.2 : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_snd.comp measurable_snd)
  have m1 : AEStronglyMeasurable (sqrtS b) μ := aestronglyMeasurable_sqrtS_of mb
  have m2 : AEStronglyMeasurable (sqrtS Sb) μ := aestronglyMeasurable_sqrtS_of mS
  have m3 : AEStronglyMeasurable (fun x => (x.2.2 : ℂ) • sqrtS Eb x) μ :=
    hη.aestronglyMeasurable.smul mE
  have heq : sqrtS (qepsOf ε b Sb Db Eb) =
      fun x => sqrtS Db x - (ε : ℂ) • ((2 : ℂ) • sqrtS Sb x + (x.2.2 : ℂ) • sqrtS Eb x + sqrtS b x) := by
    ext x i
    simp [sqrtS, qepsOf]
    ring
  rw [heq]
  exact mD.sub (((m2.const_smul (2 : ℂ)).add m3).add m1 |>.const_smul (ε : ℂ))

/-- Pointwise bound on `indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))` in terms of
`Qw = Qbε - qepsOf ε b0 Sb0 Qb0 Eb0` and the flat graph profile on `obsBox σ H₁ L₁`. -/
theorem indBox_sqrtS_q_pointwise {σ H₁ L₁ Γ ε : ℝ} (hσ : 0 < σ) (hH₁ : H₁ ≤ Γ) (hL₁ : L₁ ≤ Γ)
    (hΓ1 : 1 ≤ Γ) (hε0 : 0 < ε) (Qbε b0 Sb0 Qb0 Eb0 : CProf) (x : Coord) :
    ‖indBox σ H₁ L₁ (sqrtS (Qbε - Qb0)) x‖ ≤
      ‖indBox σ H₁ L₁ (sqrtS (Qbε - qepsOf ε b0 Sb0 Qb0 Eb0)) x‖ +
        (2 * Γ * ε) * (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖) := by
  set Qw := Qbε - qepsOf ε b0 Sb0 Qb0 Eb0
  have hRHS_nonneg : 0 ≤ ‖indBox σ H₁ L₁ (sqrtS Qw) x‖ +
      (2 * Γ * ε) * (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖) := by
    positivity
  by_cases hx : x ∈ obsBox σ H₁ L₁
  · unfold indBox
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    have hx1_pos : 0 < x.1 := lt_of_lt_of_le hσ hx.1.1
    have hx1_le : x.1 ≤ Γ := hx.1.2.trans hH₁
    have hsqrt_le : Real.sqrt x.1 ≤ Γ := by
      calc Real.sqrt x.1 ≤ Real.sqrt (Γ ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith
        _ = Γ := Real.sqrt_sq (by linarith)
    have hη_le : |x.2.2| ≤ Γ := (abs_le.mpr hx.2.2).trans hL₁
    have hsplit : sqrtS (Qbε - Qb0) x =
        sqrtS Qw x - (ε : ℂ) • ((2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x) := by
      ext i
      simp [sqrtS, Qw, qepsOf]
      ring
    rw [hsplit]
    have h1 : ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖ ≤
        2 * Γ * (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖) := by
      have nS : ‖sqrtS Sb0 x‖ ≤ Γ * ‖Sb0 x‖ := by
        rw [norm_sqrtS]
        exact mul_le_mul_of_nonneg_right hsqrt_le (norm_nonneg _)
      have nB : ‖sqrtS b0 x‖ ≤ Γ * ‖b0 x‖ := by
        rw [norm_sqrtS]
        exact mul_le_mul_of_nonneg_right hsqrt_le (norm_nonneg _)
      have nE : ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ ≤ Γ * ‖sqrtS Eb0 x‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hη_le (norm_nonneg _)
      calc ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖
          ≤ ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ := norm_add_le _ _
        _ ≤ ‖(2 : ℂ) • sqrtS Sb0 x‖ + ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ :=
            add_le_add (norm_add_le _ _) le_rfl
        _ = 2 * ‖sqrtS Sb0 x‖ + ‖(x.2.2 : ℂ) • sqrtS Eb0 x‖ + ‖sqrtS b0 x‖ := by
            simp [norm_smul]
        _ ≤ 2 * (Γ * ‖Sb0 x‖) + Γ * ‖sqrtS Eb0 x‖ + Γ * ‖b0 x‖ := by gcongr
        _ ≤ 2 * Γ * (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖) := by
            nlinarith [norm_nonneg (b0 x), norm_nonneg (Sb0 x),
              norm_nonneg (sqrtS Qb0 x), norm_nonneg (sqrtS Eb0 x)]
    calc ‖sqrtS Qw x - (ε : ℂ) • ((2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x)‖
        ≤ ‖sqrtS Qw x‖ + ‖(ε : ℂ) • ((2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x)‖ :=
          norm_sub_le _ _
      _ = ‖sqrtS Qw x‖ + ε * ‖(2 : ℂ) • sqrtS Sb0 x + (x.2.2 : ℂ) • sqrtS Eb0 x + sqrtS b0 x‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε0.le]
      _ ≤ ‖sqrtS Qw x‖ + ε * (2 * Γ * (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖)) := by
          gcongr
      _ = ‖sqrtS Qw x‖ + (2 * Γ * ε) * (‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖) := by
          ring
  · unfold indBox
    rw [Set.indicator_of_notMem hx, norm_zero]
    exact hRHS_nonneg

/-- Norm bound comparing `indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))` to
`indBox σ H₁ L₁ (sqrtS (Qbε - qepsOf ε b0 Sb0 Qb0 Eb0))` up to `O(Γ^4 √ε) ‖F‖`. -/
theorem hNorm_indBox_sqrtS_q_le_qw {c σ H₁ L₁ Γ ν ε Cf : ℝ}
    (hσ : 0 < σ) (hH₁ : H₁ ≤ Γ) (hL₁ : L₁ ≤ Γ) (hΓ1 : 1 ≤ Γ)
    (hν : 0 < ν) (hνΓ : ν⁻¹ ≤ Γ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hCf : 0 < Cf)
    {F Qbε b0 Sb0 Qb0 Eb0 : CProf}
    (mQε : AEStronglyMeasurable (sqrtS Qbε) (hMeas c 2))
    (mb0 : AEStronglyMeasurable b0 (hMeas c 2))
    (mS0 : AEStronglyMeasurable Sb0 (hMeas c 2))
    (mQ0 : AEStronglyMeasurable (sqrtS Qb0) (hMeas c 2))
    (mE0 : AEStronglyMeasurable (sqrtS Eb0) (hMeas c 2))
    (hg0 : hNorm c 2 b0 + hNorm c 2 Sb0 +
        ENNReal.ofReal (Real.sqrt ν) * (hNorm c 2 (sqrtS Qb0) + hNorm c 2 (sqrtS Eb0)) ≤
      ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c 2 F) :
    hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))) ≤
      hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Qbε - qepsOf ε b0 Sb0 Qb0 Eb0))) +
        ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F := by
  set Qw := Qbε - qepsOf ε b0 Sb0 Qb0 Eb0
  set P_Qw := indBox σ H₁ L₁ (sqrtS Qw)
  set f0 : Coord → ℝ := fun x => ‖b0 x‖ + ‖Sb0 x‖ + ‖sqrtS Qb0 x‖ + ‖sqrtS Eb0 x‖
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have mQw : AEStronglyMeasurable (sqrtS Qw) (hMeas c 2) := by
    have : sqrtS Qw = sqrtS Qbε - sqrtS (qepsOf ε b0 Sb0 Qb0 Eb0) :=
      flatCls_sqrtS_sub Qbε (qepsOf ε b0 Sb0 Qb0 Eb0)
    rw [this]
    exact mQε.sub (aestronglyMeasurable_sqrtS_qepsOf ε mb0 mS0 mQ0 mE0)
  have mPQw : AEStronglyMeasurable P_Qw (hMeas c 2) :=
    aestronglyMeasurable_indBox σ H₁ L₁ mQw
  have mf0 : AEStronglyMeasurable f0 (hMeas c 2) :=
    ((mb0.norm.add mS0.norm).add mQ0.norm).add mE0.norm
  have hmono : hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))) ≤
      eLpNorm ((fun x => ‖P_Qw x‖) + (2 * Γ * ε) • f0) (ENNReal.ofReal 2) (hMeas c 2) := by
    apply eLpNorm_mono_real
    intro x
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, P_Qw, Qw, f0] using
      indBox_sqrtS_q_pointwise hσ hH₁ hL₁ hΓ1 hε0 Qbε b0 Sb0 Qb0 Eb0 x
  have h2Γε : 0 ≤ 2 * Γ * ε := by positivity
  have hsplit : eLpNorm ((fun x => ‖P_Qw x‖) + (2 * Γ * ε) • f0) (ENNReal.ofReal 2) (hMeas c 2) ≤
      hNorm c 2 P_Qw + ENNReal.ofReal (2 * Γ * ε) * eLpNorm f0 (ENNReal.ofReal 2) (hMeas c 2) := by
    calc eLpNorm ((fun x => ‖P_Qw x‖) + (2 * Γ * ε) • f0) (ENNReal.ofReal 2) (hMeas c 2)
        ≤ eLpNorm (fun x => ‖P_Qw x‖) (ENNReal.ofReal 2) (hMeas c 2) +
            eLpNorm ((2 * Γ * ε) • f0) (ENNReal.ofReal 2) (hMeas c 2) :=
          eLpNorm_add_le mPQw.norm (mf0.const_smul _) hp1
      _ = hNorm c 2 P_Qw + ENNReal.ofReal (2 * Γ * ε) * eLpNorm f0 (ENNReal.ofReal 2) (hMeas c 2) := by
          rw [eLpNorm_norm, eLpNorm_const_smul, Real.enorm_eq_ofReal h2Γε]
          rfl
  have h40 : eLpNorm f0 (ENNReal.ofReal 2) (hMeas c 2) ≤
      ENNReal.ofReal Γ * (ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c 2 F) :=
    (eLpNorm_add4_norm_le hp1 mb0 mS0 mQ0 mE0).trans
      (graph_sum_le_of_graphBound hν hνΓ hΓ1 hg0)
  have hε_sqrt : ε ≤ Real.sqrt ε := by
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε0.le).symm
      _ ≤ Real.sqrt ε := Real.sqrt_le_sqrt (by nlinarith)
  have hΓ0 : 0 ≤ Γ := by linarith
  have hCf0 : 0 ≤ Cf * Γ ^ 2 := by positivity
  have hrem : ENNReal.ofReal (2 * Γ * ε) * eLpNorm f0 (ENNReal.ofReal 2) (hMeas c 2) ≤
      ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F := by
    calc ENNReal.ofReal (2 * Γ * ε) * eLpNorm f0 (ENNReal.ofReal 2) (hMeas c 2)
        ≤ ENNReal.ofReal (2 * Γ * ε) *
            (ENNReal.ofReal Γ * (ENNReal.ofReal (Cf * Γ ^ 2) * hNorm c 2 F)) := by gcongr
      _ = ENNReal.ofReal (2 * Cf * Γ ^ 4 * ε) * hNorm c 2 F := by
          rw [← mul_assoc (ENNReal.ofReal Γ), ← ENNReal.ofReal_mul hΓ0,
            ← mul_assoc (ENNReal.ofReal (2 * Γ * ε)),
            ← ENNReal.ofReal_mul h2Γε]
          congr 2
          ring
      _ ≤ ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F := by
          gcongr
  exact (hmono.trans hsplit).trans (add_le_add le_rfl hrem)

/-! ## Section 3: Smooth box cutoff `boxCutoff σ H₁ L₁` on `obsBox σ H₁ L₁` -/

/-- Radial factor of the box cutoff: `1` on `[σ, H₁]`, `0` outside `(σ / 2, 2 * H₁)`. -/
def sBoxCut (σ H₁ s : ℝ) : ℝ :=
  Real.smoothTransition (2 * s / σ - 1) * Real.smoothTransition ((2 * H₁ - s) / H₁)

/-- Vertical factor of the box cutoff: `1` on `[-L₁, L₁]`, `0` outside `(-L₁ - 1, L₁ + 1)`. -/
def etaBoxCut (L₁ η : ℝ) : ℝ :=
  Real.smoothTransition (L₁ + 1 + η) * Real.smoothTransition (L₁ + 1 - η)

/-- Smooth box cutoff on `Coord`: `1` on `obsBox σ H₁ L₁` and supported in
`obsBox (σ / 2) (2 * H₁) (L₁ + 1)`. -/
def boxCutoff (σ H₁ L₁ : ℝ) (x : Coord) : ℝ :=
  sBoxCut σ H₁ x.1 * etaBoxCut L₁ x.2.2

theorem boxCutoff_contDiff (σ H₁ L₁ : ℝ) : ContDiff ℝ ∞ (boxCutoff σ H₁ L₁) := by
  unfold boxCutoff sBoxCut etaBoxCut
  apply ContDiff.mul
  · apply ContDiff.mul
    · exact Real.smoothTransition.contDiff.comp (by fun_prop)
    · exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · apply ContDiff.mul
    · exact Real.smoothTransition.contDiff.comp (by fun_prop)
    · exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem sBoxCut_nonneg (σ H₁ s : ℝ) : 0 ≤ sBoxCut σ H₁ s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem sBoxCut_le_one (σ H₁ s : ℝ) : sBoxCut σ H₁ s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem etaBoxCut_nonneg (L₁ η : ℝ) : 0 ≤ etaBoxCut L₁ η :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem etaBoxCut_le_one (L₁ η : ℝ) : etaBoxCut L₁ η ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem boxCutoff_nonneg (σ H₁ L₁ : ℝ) (x : Coord) : 0 ≤ boxCutoff σ H₁ L₁ x :=
  mul_nonneg (sBoxCut_nonneg σ H₁ x.1) (etaBoxCut_nonneg L₁ x.2.2)

theorem boxCutoff_le_one (σ H₁ L₁ : ℝ) (x : Coord) : boxCutoff σ H₁ L₁ x ≤ 1 :=
  mul_le_one₀ (sBoxCut_le_one σ H₁ x.1) (etaBoxCut_nonneg L₁ x.2.2) (etaBoxCut_le_one L₁ x.2.2)

theorem boxCutoff_periodic (c σ H₁ L₁ : ℝ) (x : Coord) :
    boxCutoff σ H₁ L₁ (qShift c x) = boxCutoff σ H₁ L₁ x := rfl

theorem boxCutoff_eq_one_of_mem {σ H₁ L₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) {x : Coord}
    (hx : x ∈ obsBox σ H₁ L₁) : boxCutoff σ H₁ L₁ x = 1 := by
  have hH₁ : 0 < H₁ := lt_of_lt_of_le hσ hσH₁
  have hs1 : 1 ≤ 2 * x.1 / σ - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hσ]
    linarith [hx.1.1]
  have hs2 : 1 ≤ (2 * H₁ - x.1) / H₁ := by
    rw [le_div_iff₀ hH₁]
    linarith [hx.1.2]
  have hη1 : 1 ≤ L₁ + 1 + x.2.2 := by linarith [hx.2.2.1]
  have hη2 : 1 ≤ L₁ + 1 - x.2.2 := by linarith [hx.2.2.2]
  unfold boxCutoff sBoxCut etaBoxCut
  rw [Real.smoothTransition.one_of_one_le hs1, Real.smoothTransition.one_of_one_le hs2,
    Real.smoothTransition.one_of_one_le hη1, Real.smoothTransition.one_of_one_le hη2]
  ring

theorem boxCutoff_eq_zero_of_outside {σ H₁ L₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) {x : Coord}
    (hx : x.1 < σ / 2 ∨ 2 * H₁ < x.1 ∨ L₁ + 1 < |x.2.2|) : boxCutoff σ H₁ L₁ x = 0 := by
  have hH₁ : 0 < H₁ := lt_of_lt_of_le hσ hσH₁
  rcases hx with hs1 | hs2 | hη
  · have hle : 2 * x.1 / σ - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_iff₀ hσ]
      linarith
    unfold boxCutoff sBoxCut
    rw [Real.smoothTransition.zero_of_nonpos hle, zero_mul, zero_mul]
  · have hle : (2 * H₁ - x.1) / H₁ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hH₁.le
    unfold boxCutoff sBoxCut
    rw [Real.smoothTransition.zero_of_nonpos hle, mul_zero, zero_mul]
  · rcases lt_abs.mp hη with hη1 | hη2
    · have hle : L₁ + 1 - x.2.2 ≤ 0 := by linarith
      unfold boxCutoff etaBoxCut
      rw [Real.smoothTransition.zero_of_nonpos hle, mul_zero, mul_zero]
    · have hle : L₁ + 1 + x.2.2 ≤ 0 := by linarith
      unfold boxCutoff etaBoxCut
      rw [Real.smoothTransition.zero_of_nonpos hle, zero_mul, mul_zero]

theorem boxCutoff_eq_zero_of_notMem {σ H₁ L₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) {x : Coord}
    (hx : x ∉ obsBox (σ / 2) (2 * H₁) (L₁ + 1)) : boxCutoff σ H₁ L₁ x = 0 := by
  apply boxCutoff_eq_zero_of_outside hσ hσH₁
  by_contra hcon
  rcases not_or.mp hcon with ⟨h1, h23⟩
  rcases not_or.mp h23 with ⟨h2, h3⟩
  have habs := abs_le.mp (not_lt.mp h3)
  exact hx ⟨⟨not_lt.mp h1, not_lt.mp h2⟩, trivial, ⟨habs.1, habs.2⟩⟩

theorem driftCutoff_boxCutoff {c σ H₁ L₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) :
    DriftCutoff c (boxCutoff σ H₁ L₁) where
  smooth := boxCutoff_contDiff σ H₁ L₁
  periodic := boxCutoff_periodic c σ H₁ L₁
  supp := ⟨σ / 2, 2 * H₁, L₁ + 1, by positivity,
    fun _ hx => boxCutoff_eq_zero_of_outside hσ hσH₁ hx⟩

theorem hNorm_indBox_le_boxCutoff_smul {c σ H₁ L₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (u : CProf) :
    hNorm c 2 (indBox σ H₁ L₁ u) ≤ hNorm c 2 (fun x => (boxCutoff σ H₁ L₁ x : ℂ) • u x) := by
  apply eLpNorm_mono
  intro x
  unfold indBox
  by_cases hx : x ∈ obsBox σ H₁ L₁
  · rw [Set.indicator_of_mem hx, boxCutoff_eq_one_of_mem hσ hσH₁ hx, Complex.ofReal_one,
      one_smul]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact norm_nonneg _

theorem hNorm_boxCutoff_smul_le_enlarged {c σ H₁ L₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (u : CProf) :
    hNorm c 2 (fun x => (boxCutoff σ H₁ L₁ x : ℂ) • u x) ≤
      hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) u) := by
  apply eLpNorm_mono
  intro x
  unfold indBox
  by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
  · rw [Set.indicator_of_mem hx, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (boxCutoff_nonneg σ H₁ L₁ x)]
    calc boxCutoff σ H₁ L₁ x * ‖u x‖ ≤ 1 * ‖u x‖ :=
          mul_le_mul_of_nonneg_right (boxCutoff_le_one σ H₁ L₁ x) (norm_nonneg _)
      _ = ‖u x‖ := one_mul _
  · rw [Set.indicator_of_notMem hx, boxCutoff_eq_zero_of_notMem hσ hσH₁ hx,
      Complex.ofReal_zero, zero_smul, norm_zero]

theorem hNorm_boxCutoff_sq_smul_le_enlarged {c σ H₁ L₁ : ℝ} (hσ : 0 < σ) (hσH₁ : σ ≤ H₁) (u : CProf) :
    hNorm c 2 (fun x => ((boxCutoff σ H₁ L₁ x ^ 2 : ℝ) : ℂ) • u x) ≤
      hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) u) := by
  apply eLpNorm_mono
  intro x
  unfold indBox
  by_cases hx : x ∈ obsBox (σ / 2) (2 * H₁) (L₁ + 1)
  · rw [Set.indicator_of_mem hx, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _)]
    have hsq_le : boxCutoff σ H₁ L₁ x ^ 2 ≤ 1 := by
      have h0 := boxCutoff_nonneg σ H₁ L₁ x
      have h1 := boxCutoff_le_one σ H₁ L₁ x
      nlinarith
    calc boxCutoff σ H₁ L₁ x ^ 2 * ‖u x‖ ≤ 1 * ‖u x‖ :=
          mul_le_mul_of_nonneg_right hsq_le (norm_nonneg _)
      _ = ‖u x‖ := one_mul _
  · rw [Set.indicator_of_notMem hx, boxCutoff_eq_zero_of_notMem hσ hσH₁ hx]
    simp

/-! ## Section 4: Weak product rule for `ψ • w` (`ψ = χ²`) and `drift_identity_H2` transfer -/

/-- Directional derivative `(v · ∇) ψ` on `Coord`. -/
def vGrad (v : Coord → Fin 3 → ℝ) (ψ : Coord → ℝ) (x : Coord) : ℝ :=
  ∑ j : Fin 3, v x j * cpd j ψ x

theorem contDiff_vGrad {v : Coord → Fin 3 → ℝ} (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => v y j))
    {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) : ContDiff ℝ ∞ (vGrad v ψ) := by
  have heq : vGrad v ψ = fun x =>
      v x 0 * cpd 0 ψ x + v x 1 * cpd 1 ψ x + v x 2 * cpd 2 ψ x := by
    funext x
    unfold vGrad
    rw [Fin.sum_univ_three]
  rw [heq]
  exact (((hv 0).mul (contDiff_cpd ψ hψ 0)).add ((hv 1).mul (contDiff_cpd ψ hψ 1))).add
    ((hv 2).mul (contDiff_cpd ψ hψ 2))

theorem isCoordTest_mul_smooth {ψ φ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hφ : IsCoordTest φ) :
    IsCoordTest (fun x : Coord => ψ x * φ x) where
  smooth := hψ.mul hφ.smooth
  compact := hφ.compact.mul_left
  supp := tsupport_mul_subset_right.trans hφ.supp

theorem coordTranspose_mul_smooth {v : Coord → Fin 3 → ℝ} (d : Coord → ℝ)
    (hv : ∀ j : Fin 3, Differentiable ℝ (fun y => v y j))
    {ψ φ : Coord → ℝ} (hψ : Differentiable ℝ ψ) (hφ : Differentiable ℝ φ) (x : Coord) :
    coordTranspose v d (fun y => ψ y * φ y) x =
      ψ x * coordTranspose v d φ x - vGrad v ψ x * φ x := by
  have hj : ∀ j : Fin 3,
      cpd j (fun y => v y j * (ψ y * φ y)) x =
        cpd j ψ x * (v x j * φ x) + ψ x * cpd j (fun y => v y j * φ y) x := by
    intro j
    have heq : (fun y => v y j * (ψ y * φ y)) = (fun y => ψ y * (v y j * φ y)) := by
      funext y; ring
    rw [heq]
    have hmul : Differentiable ℝ (fun y => v y j * φ y) := (hv j).mul hφ
    have hq : cpd j (fun y => ψ y * (v y j * φ y)) x =
        ψ x * cpd j (fun y => v y j * φ y) x + (v x j * φ x) * cpd j ψ x :=
      qd_cpd_mul j hψ hmul x
    linarith [hq]
  rw [qd_coordT_eq, qd_coordT_eq, hj 0, hj 1, hj 2]
  unfold vGrad
  rw [Fin.sum_univ_three]
  ring

/-- Scalar weak product rule: if `u` has `(v, d)` weak derivative `Du` and `∂_η` weak derivative
`Eu`, then for any smooth `ψ`, `ψ u` has `(v, d)` weak derivative `ψ Du + (v · ∇ψ) u`. -/
theorem hasWeakFO_smul_smooth {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => v y j))
    {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {u Du Eu : Coord → ℂ} (hD : HasWeakFO v d u Du) (hE : HasWeakFO vEta dZero u Eu) :
    HasWeakFO v d (fun x => (ψ x : ℂ) * u x)
      (fun x => (ψ x : ℂ) * Du x + (vGrad v ψ x : ℂ) * u x) := by
  have hvd : ∀ j : Fin 3, Differentiable ℝ (fun y => v y j) :=
    fun j => (hv j).differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hvg : ContDiff ℝ ∞ (vGrad v ψ) := contDiff_vGrad hv hψ
  set Gu : Coord → ℂ := fun x => (ψ x : ℂ) * Du x + (vGrad v ψ x : ℂ) * u x
  have h_int : ∀ φ : Coord → ℝ, IsCoordTest φ →
      Integrable (fun x => ((ψ x : ℂ) * u x) * (coordTranspose v d φ x : ℂ)) ∧
        Integrable (fun x => Gu x * (φ x : ℂ)) := by
    intro φ hφ
    have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
    have hψφ : IsCoordTest (fun x => ψ x * φ x) := isCoordTest_mul_smooth hψ hφ
    have hvgφ : IsCoordTest (fun x => vGrad v ψ x * φ x) := isCoordTest_mul_smooth hvg hφ
    have i1 := (hD.1 _ hψφ).1
    have i2 := (hD.1 _ hψφ).2
    have i3 := integrable_mul_coordTest hE hvgφ
    refine ⟨?_, ?_⟩
    · have hpt : ∀ x : Coord,
          ((ψ x : ℂ) * u x) * (coordTranspose v d φ x : ℂ) =
            u x * (coordTranspose v d (fun y => ψ y * φ y) x : ℂ) +
              u x * ((vGrad v ψ x * φ x : ℝ) : ℂ) := by
        intro x
        rw [coordTranspose_mul_smooth d hvd hψd hφd x]
        push_cast
        ring
      exact (i1.add i3).congr (ae_of_all _ fun x => (hpt x).symm)
    · have hpt : ∀ x : Coord,
          Gu x * (φ x : ℂ) =
            Du x * ((ψ x * φ x : ℝ) : ℂ) + u x * ((vGrad v ψ x * φ x : ℝ) : ℂ) := by
        intro x
        dsimp [Gu]
        push_cast
        ring
      exact (i2.add i3).congr (ae_of_all _ fun x => (hpt x).symm)
  refine ⟨h_int, fun φ hφ => ?_⟩
  have hφd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hψφ : IsCoordTest (fun x => ψ x * φ x) := isCoordTest_mul_smooth hψ hφ
  have hvgφ : IsCoordTest (fun x => vGrad v ψ x * φ x) := isCoordTest_mul_smooth hvg hφ
  have i1 := (hD.1 _ hψφ).1
  have i2 := (hD.1 _ hψφ).2
  have i3 := integrable_mul_coordTest hE hvgφ
  have hpt1 : ∀ x : Coord,
      Gu x * (φ x : ℂ) =
        Du x * ((ψ x * φ x : ℝ) : ℂ) + u x * ((vGrad v ψ x * φ x : ℝ) : ℂ) := by
    intro x; dsimp [Gu]; push_cast; ring
  have hpt2 : ∀ x : Coord,
      ((ψ x : ℂ) * u x) * (coordTranspose v d φ x : ℂ) =
        u x * (coordTranspose v d (fun y => ψ y * φ y) x : ℂ) +
          u x * ((vGrad v ψ x * φ x : ℝ) : ℂ) := by
    intro x
    rw [coordTranspose_mul_smooth d hvd hψd hφd x]
    push_cast
    ring
  rw [integral_congr_ae (ae_of_all _ hpt1), integral_congr_ae (ae_of_all _ hpt2),
    integral_add i2 i3, integral_add i1 i3, hD.2 _ hψφ]

/-- Profile weak derivative of `ψ • w` (`ψ Du + (v · ∇ψ) w`). -/
def weakSmul (v : Coord → Fin 3 → ℝ) (ψ : Coord → ℝ) (w Dw : CProf) : CProf :=
  fun x => (ψ x : ℂ) • Dw x + (vGrad v ψ x : ℂ) • w x

theorem hasWeakVec_smul_smooth {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ}
    (hv : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y => v y j))
    {ψ : Coord → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {w Dw Ew : CProf} (hD : HasWeakVec v d w Dw) (hE : HasWeakVec vEta dZero w Ew) :
    HasWeakVec v d (fun x => (ψ x : ℂ) • w x) (weakSmul v ψ w Dw) :=
  fun i => hasWeakFO_smul_smooth hv hψ (hD i) (hE i)

theorem contDiff_vS (j : Fin 3) : ContDiff ℝ ∞ (fun y : Coord => vS y j) := by
  fin_cases j
  · change ContDiff ℝ ∞ (fun y : Coord => y.1); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop

theorem contDiff_vQ0 (j : Fin 3) : ContDiff ℝ ∞ (fun y : Coord => vQ0 y j) := by
  fin_cases j
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop

theorem contDiff_vQ (ε : ℝ) (j : Fin 3) : ContDiff ℝ ∞ (fun y : Coord => vQ ε y j) := by
  fin_cases j
  · change ContDiff ℝ ∞ (fun y : Coord => -2 * ε * y.1); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun y : Coord => -ε * y.2.2); fun_prop

theorem contDiff_vEta (j : Fin 3) : ContDiff ℝ ∞ (fun y : Coord => vEta y j) := by
  fin_cases j
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (0 : ℝ)); fun_prop
  · change ContDiff ℝ ∞ (fun _ : Coord => (1 : ℝ)); fun_prop

/-- `drift_identity_H2` transferred to `w = bε - b0` and any `Sw = Sbε - Sb0` with
`HasWeakVec vS dZero bε Sbε` and `HasWeakVec vS dZero b0 Sb0`. -/
theorem drift_identity_H2_given {ν c ε : ℝ} {μ : ℂ} (hc : 0 < c) (hε : 0 < ε)
    {F bε b0 Sbε Sb0 : CProf} (hbε_in : InHr c 2 bε) (hbε_resp : IsResponse ν c ε μ 2 F bε)
    (hb0_class : InFlatClass c 2 b0)
    (hSε : HasWeakVec vS dZero bε Sbε) (hS0 : HasWeakVec vS dZero b0 Sb0)
    {χ : Coord → ℝ} (hχ : DriftCutoff c χ) :
    (∫ x, ∑ i : Fin 2, (Sbε - Sb0) x i *
        (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * (bε - b0) x i) ∂(hMeas c 2)).re =
      (1 / 4) * ∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖(bε - b0) x i‖ ^ 2 ∂(hMeas c 2) -
        ∫ x, x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖(bε - b0) x i‖ ^ 2 ∂(hMeas c 2) := by
  obtain ⟨Sbε', hSε', hSbε'_in⟩ := exists_inHr_weakS_of_isResponse hc hε hbε_resp
  obtain ⟨Sb0', -, -, hS0', -, -, hSb0'_in, -, -⟩ := hb0_class.deriv
  have hw_in : InHr c 2 (bε - b0) := flatCls_inHr_sub hbε_in hb0_class.inHr
  have hSw'_in : InHr c 2 (Sbε' - Sb0') := flatCls_inHr_sub hSbε'_in hSb0'_in
  have hSw' : HasWeakVec vS dZero (bε - b0) (Sbε' - Sb0') := flatCls_hasWeakVec_sub hSε' hS0'
  have hSw : HasWeakVec vS dZero (bε - b0) (Sbε - Sb0) := flatCls_hasWeakVec_sub hSε hS0
  have hae : ∀ᵐ x ∂(hMeas c 2), (Sbε - Sb0) x = (Sbε' - Sb0') x :=
    hasWeakVec_unique_ae hc hSw hSw'
  have hint_eq :
      ∫ x, ∑ i : Fin 2, (Sbε - Sb0) x i *
          (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * (bε - b0) x i) ∂(hMeas c 2) =
        ∫ x, ∑ i : Fin 2, (Sbε' - Sb0') x i *
          (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * (bε - b0) x i) ∂(hMeas c 2) := by
    refine integral_congr_ae (hae.mono fun x hx => ?_)
    simp [hx]
  rw [hint_eq]
  exact drift_identity_H2 c (bε - b0) (Sbε' - Sb0') χ hc hw_in hSw'_in hSw' hχ

/-! ## Section 5: Leaf propositions and conditional assembly of `TestedGradientEnergyH2` -/

theorem re_ofReal_mul (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
  simp [Complex.mul_re]

theorem re_ofReal_mul_ofReal_mul (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * z).re = a * b * z.re := by
  simp [Complex.mul_re]

/-- **Leaf 1 (`SubtractedChartTestedEq`, `PartII-b:T16/2/1`, SP 1959-1960 & 1978-1981)**:
Chart-level subtracted weak equation for `w = bε - b0` tested against `t = χ² • w`
(`χ = boxCutoff σ H₁ L₁`, `Qv = qepsOf ε b0 Sb0 Qb0 Eb0`, `Qw = Qbε - Qv`, `Ew = Ebε - Eb0`,
`Qt = weakSmul (vQ ε) (fun x => χ x ^ 2) w Qw`,
`Dt = weakSmul vQ0 (fun x => χ x ^ 2) w (dqOf ε bε Sbε Qbε Ebε - Qb0)`,
`Et = weakSmul vEta (fun x => χ x ^ 2) w Ew`):
testing `IsResponse ν c ε μ 2 F bε` and `IsFlatResponse ν μ F b0` against `χ² • w`,
bounding the source difference `Re ⟨(P_ε - P_0) F, χ² w⟩_{H_2}` by `O(Γ^k) ω ‖F‖_{H_2}²`,
and retaining the nonnegative radial frame energy on `w` up to the `O(Γ^k ε)` radial frame
discrepancy on `b0`. -/
def SubtractedChartTestedEq : Prop :=
  ∃ (k_chart : ℕ) (C_chart : ℝ), 0 < C_chart ∧
    ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
      H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 4 → 0 < ν → 0 < c → 0 < σ →
      σ ≤ H₁ → 0 ≤ L₁ →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
    ∀ F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 : CProf,
      InHr c 2 F → InHr c 2 bε → IsResponse ν c ε μ 2 F bε →
      IsFlatResponse ν μ F b0 → InFlatClass c 2 b0 →
      HasWeakVec vS dZero bε Sbε → HasWeakVec (vQ ε) (dQ ε) bε Qbε →
      HasWeakVec vEta dZero bε Ebε →
      AEStronglyMeasurable Sbε (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Qbε) (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Ebε) (hMeas c 2) →
      HasWeakVec vS dZero b0 Sb0 → HasWeakVec vQ0 dZero b0 Qb0 →
      HasWeakVec vEta dZero b0 Eb0 →
      AEStronglyMeasurable Sb0 (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Qb0) (hMeas c 2) →
      AEStronglyMeasurable (sqrtS Eb0) (hMeas c 2) →
    ∀ om : ℝ, 0 ≤ om →
      hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) (bε - b0)) ≤
        ENNReal.ofReal om * hNorm c 2 F →
      let χ := boxCutoff σ H₁ L₁
      let ψ := fun x : Coord => χ x ^ 2
      let w := bε - b0
      let Sw := Sbε - Sb0
      let Dw := dqOf ε bε Sbε Qbε Ebε - Qb0
      let Qv := qepsOf ε b0 Sb0 Qb0 Eb0
      let Qw := Qbε - Qv
      let Ew := Ebε - Eb0
      let Dt := weakSmul vQ0 ψ w Dw
      let Qt := weakSmul (vQ ε) ψ w Qw
      let Et := weakSmul vEta ψ w Ew
      μ.re * ∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) +
        (∫ x, ∑ i : Fin 2, Sw x i * (starRingEnd ℂ) (((χ x ^ 2 : ℝ) : ℂ) * w x i) ∂(hMeas c 2)).re +
        ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qw x i * (starRingEnd ℂ) (Qt x i) ∂(hMeas c 2)).re -
        ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          (Qb0 x i * (starRingEnd ℂ) (Dt x i) - Qv x i * (starRingEnd ℂ) (Qt x i)) ∂(hMeas c 2)).re +
        ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ew x i * (starRingEnd ℂ) (Et x i) ∂(hMeas c 2)).re ≤
        C_chart * Γ ^ k_chart * (om + om ^ 2 + ε) * (hNorm c 2 F).toReal ^ 2

/-- **Energy inequality after applying `drift_identity_H2` and `diffusion_difference_terms`**
(SP 1961-1977): eliminates the damping+drift term using `(μ.re + 1/4) ≥ Γ⁻¹ > 0` and
`drift_identity_H2_given`, and expands the `q`-diffusion difference into the two `L_1` terms using
`diffusion_difference_terms` and `hasWeakVec_smul_smooth`. -/
theorem subtracted_chart_energy_ineq (hChart : SubtractedChartTestedEq) :
    ∃ (k_chart : ℕ) (C_chart : ℝ), 0 < C_chart ∧
      ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
        H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 4 → 0 < ν → 0 < c → 0 < σ →
        σ ≤ H₁ → 0 ≤ L₁ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
      ∀ F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 : CProf,
        InHr c 2 F → InHr c 2 bε → IsResponse ν c ε μ 2 F bε →
        IsFlatResponse ν μ F b0 → InFlatClass c 2 b0 →
        HasWeakVec vS dZero bε Sbε → HasWeakVec (vQ ε) (dQ ε) bε Qbε →
        HasWeakVec vEta dZero bε Ebε →
        AEStronglyMeasurable Sbε (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Qbε) (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Ebε) (hMeas c 2) →
        HasWeakVec vS dZero b0 Sb0 → HasWeakVec vQ0 dZero b0 Qb0 →
        HasWeakVec vEta dZero b0 Eb0 →
        AEStronglyMeasurable Sb0 (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Qb0) (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Eb0) (hMeas c 2) →
      ∀ om : ℝ, 0 ≤ om →
        hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) (bε - b0)) ≤
          ENNReal.ofReal om * hNorm c 2 F →
        let χ := boxCutoff σ H₁ L₁
        let ψ := fun x : Coord => χ x ^ 2
        let w := bε - b0
        let Sw := Sbε - Sb0
        let Qv := qepsOf ε b0 Sb0 Qb0 Eb0
        let Qw := Qbε - Qv
        let Ew := Ebε - Eb0
        let t : CProf := fun x => (ψ x : ℂ) • w x
        let St := weakSmul vS ψ w Sw
        let Qt := weakSmul (vQ ε) ψ w Qw
        let Et := weakSmul vEta ψ w Ew
        ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qw x i * (starRingEnd ℂ) (Qt x i) ∂(hMeas c 2)).re +
          ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ew x i * (starRingEnd ℂ) (Et x i) ∂(hMeas c 2)).re ≤
          ∫ x, x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) +
            ν * ε * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
              ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
                Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i))
              ∂(hMeas c 2)).re +
            C_chart * Γ ^ k_chart * (om + om ^ 2 + ε) * (hNorm c 2 F).toReal ^ 2 := by
  obtain ⟨k_chart, C_chart, hC_chart, hC⟩ := hChart
  refine ⟨k_chart, C_chart, hC_chart, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ hσH₁ hL₁0
    ε hε0 hε1 hP F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 hF hbε_in hbε_resp hb0_resp hb0_class
    hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0 om hom0 hom
  dsimp only
  set χ := boxCutoff σ H₁ L₁
  set ψ : Coord → ℝ := fun x => χ x ^ 2
  set w := bε - b0
  set Sw := Sbε - Sb0
  set Dw := dqOf ε bε Sbε Qbε Ebε - Qb0
  set Qv := qepsOf ε b0 Sb0 Qb0 Eb0
  set Qw := Qbε - Qv
  set Ew := Ebε - Eb0
  set t : CProf := fun x => (ψ x : ℂ) • w x
  set St := weakSmul vS ψ w Sw
  set Dt := weakSmul vQ0 ψ w Dw
  set Qt := weakSmul (vQ ε) ψ w Qw
  set Et := weakSmul vEta ψ w Ew
  have hχ : DriftCutoff c χ := driftCutoff_boxCutoff hσ hσH₁
  have hψ : ContDiff ℝ ∞ ψ := hχ.smooth.pow 2
  have hQv : HasWeakVec (vQ ε) (dQ ε) b0 Qv := hasWeakVec_qepsOf ε hS0 hQ0 hE0
  have hDbε : HasWeakVec vQ0 dZero bε (dqOf ε bε Sbε Qbε Ebε) := hasWeakVec_dqOf ε hSε hQε hEε
  have hSw : HasWeakVec vS dZero w Sw := flatCls_hasWeakVec_sub hSε hS0
  have hDw : HasWeakVec vQ0 dZero w Dw := flatCls_hasWeakVec_sub hDbε hQ0
  have hQw : HasWeakVec (vQ ε) (dQ ε) w Qw := flatCls_hasWeakVec_sub hQε hQv
  have hEw : HasWeakVec vEta dZero w Ew := flatCls_hasWeakVec_sub hEε hE0
  have hSt : HasWeakVec vS dZero t St := hasWeakVec_smul_smooth contDiff_vS hψ hSw hEw
  have hDt : HasWeakVec vQ0 dZero t Dt := hasWeakVec_smul_smooth contDiff_vQ0 hψ hDw hEw
  have hQt : HasWeakVec (vQ ε) (dQ ε) t Qt := hasWeakVec_smul_smooth (contDiff_vQ ε) hψ hQw hEw
  have hEt : HasWeakVec vEta dZero t Et := hasWeakVec_smul_smooth contDiff_vEta hψ hEw hEw
  have h_drift := drift_identity_H2_given hc hε0 hbε_in hbε_resp hb0_class hSε hS0 hχ
  have h_diff_c := diffusion_difference_terms c ε ν b0 Qb0 Qv Sb0 Eb0 t Dt Qt St Et
    hc hQ0 hQv hS0 hE0 hDt hQt hSt hEt
  have h_diff :
      ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          (Qb0 x i * (starRingEnd ℂ) (Dt x i) - Qv x i * (starRingEnd ℂ) (Qt x i)) ∂(hMeas c 2)).re =
        ν * ε * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
          ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
            Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i)) ∂(hMeas c 2)).re := by
    have hre := congrArg Complex.re h_diff_c
    rwa [re_ofReal_mul, re_ofReal_mul_ofReal_mul] at hre
  have h_chart := hC Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap
    hν hc hσ hσH₁ hL₁0 ε hε0 hε1 hP F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 hF hbε_in hbε_resp
    hb0_resp hb0_class hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0 om hom0 hom
  dsimp only at h_chart
  have h_int_nonneg : 0 ≤ ∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) := by
    apply integral_nonneg
    intro x
    positivity
  have hμ_pos : 0 < μ.re + 1 / 4 := lt_of_lt_of_le (by positivity : (0 : ℝ) < Γ⁻¹) hgap
  have h_damp_nonneg :
      0 ≤ (μ.re + 1 / 4) * ∫ x, χ x ^ 2 * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) :=
    mul_nonneg hμ_pos.le h_int_nonneg
  linarith

/-- **Leaf 2 (`BoxDiffusionAbsorption`, `PartII-b:T16/2/2`, SP 1963-1977 & 1982-1985)**:
From the drift-and-diffusion-expanded energy inequality for `w = bε - b0`, the `r = 2` graph bounds
for `(bε, Sbε, Qbε, Ebε)` and `(b0, Sb0, Qb0, Eb0)`, and the enlarged-box bound `om` on `w`:
absorb `1/4` of the gradient energy from the first diffusion difference term
`ν ε ⟨√s L_1 b0, √s Qt⟩`, bound the second diffusion difference term `ν ε ⟨√s Qb0, √s L_1 t⟩` by
`O(Γ^k ε) ‖F‖²`, and bound the diffusion cutoff terms and drift cutoff term
`∫ s χ χ_s |w|² dH_2` by `1/4` of the gradient energy plus `C Γ^k om² ‖F‖²` to conclude the
`χ`-weighted `H_2` bound on `(sqrtS Qw, sqrtS Ew)`. -/
def BoxDiffusionAbsorption : Prop :=
  ∀ (k_chart : ℕ) (C_chart : ℝ), 0 < C_chart →
    ∃ (k_abs : ℕ) (C_abs : ℝ), 0 < C_abs ∧
      ∀ (Γ ν c σ H₁ L₁ : ℝ) (μ : ℂ), 1 ≤ Γ → ν ≤ Γ → ν⁻¹ ≤ Γ → c ≤ Γ → c⁻¹ ≤ Γ → σ⁻¹ ≤ Γ →
        H₁ ≤ Γ → L₁ ≤ Γ → ‖μ‖ ≤ Γ → Γ⁻¹ ≤ μ.re + 1 / 4 → 0 < ν → 0 < c → 0 < σ →
        σ ≤ H₁ → 0 ≤ L₁ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
      ∀ F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 : CProf,
        InHr c 2 F → InHr c 2 bε → IsResponse ν c ε μ 2 F bε →
        IsFlatResponse ν μ F b0 → InFlatClass c 2 b0 →
        HasWeakVec vS dZero bε Sbε → HasWeakVec (vQ ε) (dQ ε) bε Qbε →
        HasWeakVec vEta dZero bε Ebε →
        AEStronglyMeasurable Sbε (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Qbε) (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Ebε) (hMeas c 2) →
        HasWeakVec vS dZero b0 Sb0 → HasWeakVec vQ0 dZero b0 Qb0 →
        HasWeakVec vEta dZero b0 Eb0 →
        AEStronglyMeasurable Sb0 (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Qb0) (hMeas c 2) →
        AEStronglyMeasurable (sqrtS Eb0) (hMeas c 2) →
      ∀ om : ℝ, 0 ≤ om →
        hNorm c 2 (indBox (σ / 2) (2 * H₁) (L₁ + 1) (bε - b0)) ≤
          ENNReal.ofReal om * hNorm c 2 F →
        let χ := boxCutoff σ H₁ L₁
        let ψ := fun x : Coord => χ x ^ 2
        let w := bε - b0
        let Sw := Sbε - Sb0
        let Qv := qepsOf ε b0 Sb0 Qb0 Eb0
        let Qw := Qbε - Qv
        let Ew := Ebε - Eb0
        let t : CProf := fun x => (ψ x : ℂ) • w x
        let St := weakSmul vS ψ w Sw
        let Qt := weakSmul (vQ ε) ψ w Qw
        let Et := weakSmul vEta ψ w Ew
        (ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Qw x i * (starRingEnd ℂ) (Qt x i) ∂(hMeas c 2)).re +
          ν * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2, Ew x i * (starRingEnd ℂ) (Et x i) ∂(hMeas c 2)).re ≤
          ∫ x, x.1 * χ x * cpd 0 χ x * ∑ i : Fin 2, ‖w x i‖ ^ 2 ∂(hMeas c 2) +
            ν * ε * (∫ x, (x.1 : ℂ) * ∑ i : Fin 2,
              ((2 * Sb0 x i + (x.2.2 : ℂ) * Eb0 x i + b0 x i) * (starRingEnd ℂ) (Qt x i) +
                Qb0 x i * (starRingEnd ℂ) (2 * St x i + (x.2.2 : ℂ) * Et x i + t x i))
              ∂(hMeas c 2)).re +
            C_chart * Γ ^ k_chart * (om + om ^ 2 + ε) * (hNorm c 2 F).toReal ^ 2) →
        hNorm c 2 (fun x => (χ x : ℂ) • sqrtS Qw x) +
            hNorm c 2 (fun x => (χ x : ℂ) • sqrtS Ew x) ≤
          ENNReal.ofReal (C_abs * Γ ^ k_abs * (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F

/-- **Conditional assembly of `TestedGradientEnergyH2`** (`PartII-b:T16/2`, SP 1955-1988) from
`SubtractedChartTestedEq` (`PartII-b:T16/2/1`) and `BoxDiffusionAbsorption`
(`PartII-b:T16/2/2`). -/
theorem testedGradientEnergyH2_of (hChart : SubtractedChartTestedEq)
    (hAbs : BoxDiffusionAbsorption) : TestedGradientEnergyH2 := by
  obtain ⟨Cf, hCf, hflat2⟩ := flat_graph_poly_two_given
  obtain ⟨k_chart, C_chart, hC_chart, hIne⟩ := subtracted_chart_energy_ineq hChart
  obtain ⟨k_abs, C_abs, hC_abs, hAbs2⟩ := hAbs k_chart C_chart hC_chart
  refine ⟨k_abs + 4, C_abs + 2 * Cf, by positivity, ?_⟩
  intro Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap hν hc hσ hσH₁ hL₁0
    ε hε0 hε1 hP F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 hF hbε_in hbε_resp hb0_resp hb0_class
    hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0 om hom0 hom
  have h_energy := hIne Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap
    hν hc hσ hσH₁ hL₁0 ε hε0 hε1 hP F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 hF hbε_in hbε_resp
    hb0_resp hb0_class hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0 om hom0 hom
  have h_chi := hAbs2 Γ ν c σ H₁ L₁ μ hΓ1 hνΓ1 hνΓ h_cΓ h_cinvΓ hσΓ hH₁ hL₁ hμΓ hgap
    hν hc hσ hσH₁ hL₁0 ε hε0 hε1 hP F bε b0 Sbε Qbε Ebε Sb0 Qb0 Eb0 hF hbε_in hbε_resp
    hb0_resp hb0_class hSε hQε hEε mSε mQε mEε hS0 hQ0 hE0 mS0 mQ0 mE0 om hom0 hom h_energy
  set χ := boxCutoff σ H₁ L₁
  set Qv := qepsOf ε b0 Sb0 Qb0 Eb0
  set Qw := Qbε - Qv
  set Ew := Ebε - Eb0
  have hg0 := hflat2 Γ ν c μ hΓ1 hμΓ hgap hν hc F b0 Sb0 Qb0 Eb0 hF hb0_resp hb0_class
    hS0 hQ0 hE0
  have hQ_box_qw :
      hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))) ≤
        hNorm c 2 (indBox σ H₁ L₁ (sqrtS Qw)) +
          ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F :=
    hNorm_indBox_sqrtS_q_le_qw hσ hH₁ hL₁ hΓ1 hν hνΓ hε0 hε1 hCf
      mQε hb0_class.inHr.meas mS0 mQ0 mE0 hg0
  have hQw_ind_chi :
      hNorm c 2 (indBox σ H₁ L₁ (sqrtS Qw)) ≤ hNorm c 2 (fun x => (χ x : ℂ) • sqrtS Qw x) :=
    hNorm_indBox_le_boxCutoff_smul hσ hσH₁ (sqrtS Qw)
  have hEw_ind_chi :
      hNorm c 2 (indBox σ H₁ L₁ (sqrtS Ew)) ≤ hNorm c 2 (fun x => (χ x : ℂ) • sqrtS Ew x) :=
    hNorm_indBox_le_boxCutoff_smul hσ hσH₁ (sqrtS Ew)
  have h_rate_nonneg : 0 ≤ Real.sqrt om + om + Real.sqrt ε := by positivity
  have h_c1_nonneg : 0 ≤ C_abs * Γ ^ k_abs * (Real.sqrt om + om + Real.sqrt ε) := by positivity
  have h_c2_nonneg : 0 ≤ 2 * Cf * Γ ^ 4 * Real.sqrt ε := by positivity
  have h_coeff_le :
      C_abs * Γ ^ k_abs * (Real.sqrt om + om + Real.sqrt ε) + 2 * Cf * Γ ^ 4 * Real.sqrt ε ≤
        (C_abs + 2 * Cf) * Γ ^ (k_abs + 4) * (Real.sqrt om + om + Real.sqrt ε) := by
    have hΓ_k1 : Γ ^ k_abs ≤ Γ ^ (k_abs + 4) :=
      pow_le_pow_right₀ hΓ1 (Nat.le_add_right k_abs 4)
    have hΓ_k2 : Γ ^ 4 ≤ Γ ^ (k_abs + 4) :=
      pow_le_pow_right₀ hΓ1 (Nat.le_add_left 4 k_abs)
    have h_sqe_le : Real.sqrt ε ≤ Real.sqrt om + om + Real.sqrt ε := by
      linarith [Real.sqrt_nonneg om]
    have t1 : C_abs * Γ ^ k_abs * (Real.sqrt om + om + Real.sqrt ε) ≤
        C_abs * Γ ^ (k_abs + 4) * (Real.sqrt om + om + Real.sqrt ε) := by
      gcongr
    have t2 : 2 * Cf * Γ ^ 4 * Real.sqrt ε ≤
        2 * Cf * Γ ^ (k_abs + 4) * (Real.sqrt om + om + Real.sqrt ε) := by
      calc 2 * Cf * Γ ^ 4 * Real.sqrt ε
          ≤ 2 * Cf * Γ ^ (k_abs + 4) * Real.sqrt ε := by gcongr
        _ ≤ 2 * Cf * Γ ^ (k_abs + 4) * (Real.sqrt om + om + Real.sqrt ε) := by gcongr
    linarith
  calc hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Qbε - Qb0))) +
        hNorm c 2 (indBox σ H₁ L₁ (sqrtS (Ebε - Eb0)))
      ≤ (hNorm c 2 (indBox σ H₁ L₁ (sqrtS Qw)) +
          ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F) +
          hNorm c 2 (indBox σ H₁ L₁ (sqrtS Ew)) :=
        add_le_add hQ_box_qw le_rfl
    _ = (hNorm c 2 (indBox σ H₁ L₁ (sqrtS Qw)) + hNorm c 2 (indBox σ H₁ L₁ (sqrtS Ew))) +
          ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F := by
        abel
    _ ≤ (hNorm c 2 (fun x => (χ x : ℂ) • sqrtS Qw x) +
          hNorm c 2 (fun x => (χ x : ℂ) • sqrtS Ew x)) +
          ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F :=
        add_le_add (add_le_add hQw_ind_chi hEw_ind_chi) le_rfl
    _ ≤ ENNReal.ofReal (C_abs * Γ ^ k_abs * (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F +
          ENNReal.ofReal (2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F :=
        add_le_add h_chi le_rfl
    _ = ENNReal.ofReal (C_abs * Γ ^ k_abs * (Real.sqrt om + om + Real.sqrt ε) +
          2 * Cf * Γ ^ 4 * Real.sqrt ε) * hNorm c 2 F := by
        rw [← add_mul, ENNReal.ofReal_add h_c1_nonneg h_c2_nonneg]
    _ ≤ ENNReal.ofReal ((C_abs + 2 * Cf) * Γ ^ (k_abs + 4) *
          (Real.sqrt om + om + Real.sqrt ε)) * hNorm c 2 F := by
        gcongr

end UnforcedLeray.Short.IIb

end
