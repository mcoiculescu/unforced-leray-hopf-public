import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_1_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransCommPoint
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.TableSupport
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Decay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_5.Pointwise.Cutoff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Assembly

/-!
# `PartIII-b:C/rep/8/1/1/2/3/1`: the commutator `YB` of a separated source is differentiable

Source `the November 2 reference manuscript` 4203-4214, 3700-3712.  At every point
off the axis `[D_{μ+1}, 𝒞_y]X₀ = tcComm` (the explicit commutator, `tcLeibniz` on the annulus,
both sides vanishing off it), and `tcComm` is a combination of `X₀`, `∇X₀` and `Ψ_{X₀}` with smooth
coefficients, of class `C¹` since `X₀`, `Ψ_{X₀}` are `C²` (`tcReg`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3

/-! ## Local invariance of `physDmu` -/

theorem physDmu_congr_local {ν m : ℝ} {X X' : ℝ → Space → Space} {τ : ℝ} {y : Space}
    (h : ∀ t, X t =ᶠ[𝓝 y] X' t) : physDmu ν m X τ y = physDmu ν m X' τ y := by
  have h1 : X τ =ᶠ[𝓝 y] X' τ := h τ
  have hd : deriv (fun t => X t y) τ = deriv (fun t => X' t y) τ := by
    congr 1
    funext t
    exact (h t).self_of_nhds
  have h2 : ∀ᶠ y' in 𝓝 y, X τ =ᶠ[𝓝 y'] X' τ := h1.eventuallyEq_nhds
  have hp : ∀ l : Fin 3, (fun y' => physPd (X τ) l y') =ᶠ[𝓝 y] fun y' => physPd (X' τ) l y' := by
    intro l
    filter_upwards [h2] with y' hy'
    unfold physPd
    rw [hy'.fderiv_eq]
  have hlap : physLap (X τ) y = physLap (X' τ) y := by
    unfold physLap physPd2
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (fun L => L (coordinateVector j)) ((hp j).fderiv_eq (𝕜 := ℝ))
  unfold physDmu
  rw [hd, h1.fderiv_eq, hlap, h1.self_of_nhds]

theorem physDmu_zero (ν m : ℝ) (τ : ℝ) (y : Space) :
    physDmu ν m (fun _ _ => (0 : Space)) τ y = 0 := by
  unfold physDmu physLap physPd2 physPd
  simp

/-! ## The cutoff coefficients -/

/-- Region in which the stream cutoff is locally constant. -/
def tcOut (ν R r : ℝ) : Prop := ν * (R ^ 2 / r ^ 2) < 4 / 5 ∨ 1 < ν * (R ^ 2 / r ^ 2)

theorem tcOut_eventually {ν R r : ℝ} (hr : r ≠ 0) (h : tcOut ν R r) :
    ∀ᶠ r' in 𝓝 r, tcOut ν R r' := by
  have hc : ContinuousAt (fun r' : ℝ => ν * (R ^ 2 / r' ^ 2)) r :=
    (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hr)).const_mul ν
  rcases h with h | h
  · filter_upwards [hc.eventually_lt continuousAt_const h] with r' hr' using Or.inl hr'
  · filter_upwards [continuousAt_const.eventually_lt hc h] with r' hr' using Or.inr hr'

theorem tcC0_eventuallyEq {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {r : ℝ} (hr : r ≠ 0)
    (h : tcOut ν R r) : ∃ c : ℝ, tcC0 ν R χy =ᶠ[𝓝 r] fun _ => c := by
  rcases h with h | h
  · refine ⟨1, ?_⟩
    have hc : ContinuousAt (fun r' : ℝ => ν * (R ^ 2 / r' ^ 2)) r :=
      (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hr)).const_mul ν
    filter_upwards [hc.eventually_lt continuousAt_const h] with r' hr'
    exact hχ.one _ hr'.le
  · refine ⟨0, ?_⟩
    have hc : ContinuousAt (fun r' : ℝ => ν * (R ^ 2 / r' ^ 2)) r :=
      (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hr)).const_mul ν
    filter_upwards [continuousAt_const.eventually_lt hc h] with r' hr'
    exact hχ.zero _ hr'.le

theorem tcF0_eq_zero {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {r : ℝ}
    (h : tcOut ν R r) : tcF0 ν R χy r = 0 := by
  have : deriv χy (ν * (R ^ 2 / r ^ 2)) = 0 := by
    rcases h with h | h
    · exact (wgx_deriv_zero_lt hχ h).1
    · exact (wgx_deriv_zero_gt hχ h).1
  simp [tcF0, this]

theorem tc_coeff_zero {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {r : ℝ} (hr : r ≠ 0)
    (h : tcOut ν R r) :
    tcA1 ν R χy r = 0 ∧ tcA2 ν R χy r = 0 ∧ tcB1 ν R χy r = 0 ∧ tcB2 ν R χy r = 0 := by
  obtain ⟨c, hc⟩ := tcC0_eventuallyEq hχ hr h
  have hd1 : deriv (tcC0 ν R χy) =ᶠ[𝓝 r] fun _ => 0 := by
    have := hc.deriv
    simpa using this
  have hD1 : deriv (tcC0 ν R χy) r = 0 := hd1.self_of_nhds
  have hD2 : deriv (deriv (tcC0 ν R χy)) r = 0 := by
    rw [hd1.deriv_eq]; simp
  have hF : tcF0 ν R χy =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [tcOut_eventually hr h] with r' hr' using tcF0_eq_zero hχ hr'
  have hf1 : deriv (tcF0 ν R χy) =ᶠ[𝓝 r] fun _ => 0 := by
    have := hF.deriv
    simpa using this
  have hF0 : tcF0 ν R χy r = 0 := hF.self_of_nhds
  have hF1 : deriv (tcF0 ν R χy) r = 0 := hf1.self_of_nhds
  have hF2 : deriv (deriv (tcF0 ν R χy)) r = 0 := by
    rw [hf1.deriv_eq]; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [tcA1, hD1, hD2]
  · simp [tcA2, hD1]
  · simp [tcB1, hF0, hF1, hF2]
  · simp [tcB2, hF0, hF1]

theorem tcComm_eventually_zero {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) (h : tcOut ν R (ϱ y)) :
    tcComm ν R χy Z τ =ᶠ[𝓝 y] fun _ => 0 := by
  have hev : ∀ᶠ y' in 𝓝 y, tcOut ν R (ϱ y') :=
    (continuous_ϱ.continuousAt).eventually (tcOut_eventually hy.ne' h)
  have hpos : ∀ᶠ y' in 𝓝 y, 0 < ϱ y' :=
    (continuous_ϱ.continuousAt).eventually (lt_mem_nhds hy)
  filter_upwards [hev, hpos] with y' h1 h2
  obtain ⟨a1, a2, b1, b2⟩ := tc_coeff_zero hχ h2.ne' h1
  simp [tcComm, a1, a2, b1, b2]

/-! ## Smoothness of the coefficients -/

theorem cdOn_deriv {f : ℝ → ℝ} (h : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi 0)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) (Ioi 0) :=
  ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 h).2

theorem tcC0_cdOn {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tcC0 ν R χy) (Ioi 0) := by
  unfold tcC0
  refine hχ.smooth.comp_contDiffOn ?_
  refine contDiffOn_const.mul (contDiffOn_const.div ((contDiffOn_id).pow 2) ?_)
  intro r hr
  exact pow_ne_zero 2 (ne_of_gt hr)

theorem tcF0_cdOn {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tcF0 ν R χy) (Ioi 0) := by
  unfold tcF0
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ => deriv χy (ν * (R ^ 2 / r ^ 2)))
      (Ioi 0) := by
    refine (wgx_chi_smooth hχ).comp_contDiffOn ?_
    refine contDiffOn_const.mul (contDiffOn_const.div ((contDiffOn_id).pow 2) ?_)
    intro r hr
    exact pow_ne_zero 2 (ne_of_gt hr)
  refine ((h1.mul (contDiffOn_const.div ((contDiffOn_id).pow 3) ?_)).div contDiffOn_id ?_)
  · intro r hr
    exact pow_ne_zero 3 (ne_of_gt hr)
  · intro r hr
    exact ne_of_gt hr

theorem tcCoeff_diffAt {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy) {r : ℝ} (hr : 0 < r) :
    DifferentiableAt ℝ (tcA1 ν R χy) r ∧ DifferentiableAt ℝ (tcA2 ν R χy) r ∧
    DifferentiableAt ℝ (tcB1 ν R χy) r ∧ DifferentiableAt ℝ (tcB2 ν R χy) r := by
  have hc0 := tcC0_cdOn (ν := ν) (R := R) hχ
  have hc1 := cdOn_deriv hc0
  have hc2 := cdOn_deriv hc1
  have hf0 := tcF0_cdOn (ν := ν) (R := R) hχ
  have hf1 := cdOn_deriv hf0
  have hf2 := cdOn_deriv hf1
  have hmem : Ioi (0 : ℝ) ∈ 𝓝 r := isOpen_Ioi.mem_nhds hr
  have d : ∀ {f : ℝ → ℝ}, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi 0) →
      DifferentiableAt ℝ f r := fun {f} h =>
    ((h.contDiffAt hmem).differentiableAt (by simp))
  have dc1 := d hc1
  have dc2 := d hc2
  have df0 := d hf0
  have df1 := d hf1
  have df2 := d hf2
  have dr : DifferentiableAt ℝ (fun r : ℝ => r) r := differentiableAt_id
  have hne : r ≠ 0 := hr.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tcA1
    fun_prop (disch := exact hne)
  · unfold tcA2
    fun_prop (disch := exact hne)
  · unfold tcB1
    fun_prop (disch := exact hne)
  · unfold tcB2
    fun_prop (disch := exact hne)

/-! ## The commutator is differentiable -/

theorem not_axis_of_pos {y : Space} (hy : 0 < ϱ y) : y ∉ axis := fun h => by
  have := (mem_axis_iff y).1 h
  linarith

theorem radialUnit_diffAt {y : Space} (hy : 0 < ϱ y) : DifferentiableAt ℝ radialUnit y := by
  have hϱ : DifferentiableAt ℝ ϱ y := (hasFDerivAt_ϱ (not_axis_of_pos hy)).differentiableAt
  have hvec : DifferentiableAt ℝ (fun y' : Space => (!₂[y' 0, y' 1, 0] : Space)) y := by
    rw [differentiableAt_piLp]
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (hϱ.inv hy.ne').smul hvec

theorem tcComm_diffAt {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : 0 < ϱ y)
    (hZ : ContDiffAt ℝ 2 (Z τ) y) (hψ : ContDiffAt ℝ 2 (psiFld Z τ) y) :
    DifferentiableAt ℝ (tcComm ν R χy Z τ) y := by
  have hϱ : DifferentiableAt ℝ ϱ y := (hasFDerivAt_ϱ (not_axis_of_pos hy)).differentiableAt
  obtain ⟨a1, a2, b1, b2⟩ := tcCoeff_diffAt (ν := ν) (R := R) hχ hy
  have hA1 : DifferentiableAt ℝ (fun y' => tcA1 ν R χy (ϱ y')) y := a1.comp y hϱ
  have hA2 : DifferentiableAt ℝ (fun y' => tcA2 ν R χy (ϱ y')) y := a2.comp y hϱ
  have hB1 : DifferentiableAt ℝ (fun y' => tcB1 ν R χy (ϱ y')) y := b1.comp y hϱ
  have hB2 : DifferentiableAt ℝ (fun y' => tcB2 ν R χy (ϱ y')) y := b2.comp y hϱ
  have hZd : DifferentiableAt ℝ (Z τ) y := hZ.differentiableAt (by norm_num)
  have hDZ : DifferentiableAt ℝ (fderiv ℝ (Z τ)) y :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hrad := radialUnit_diffAt hy
  have hpsi : DifferentiableAt ℝ (fun y' => outPrim Z τ (ϱ y') (y' 2)) y := by
    have h1 := hψ.differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun y' => (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)
        (psiFld Z τ y')) y := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt.comp
          y h1
    simpa [psiFld, coordinateVector] using h2
  have hz2 : DifferentiableAt ℝ (fun y' => Z τ y' 2) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).differentiableAt.comp y hZd
  unfold tcComm
  exact ((hA1.smul hZd).add (hA2.smul (hDZ.clm_apply hrad))).add
    (((hB1.mul hpsi).add (hB2.mul hz2)).smul_const _)

/-! ## `sepComm = tcComm` -/

theorem tcOut_iff_not_mem {ν R : ℝ} (hν : 0 < ν) (hR : 0 < R) {y : Space} (hy : 0 < ϱ y) :
    tcOut ν R (ϱ y) ↔ y ∉ streamAnn ν R := by
  have hρ2 : 0 < ϱ y ^ 2 := pow_pos hy 2
  have hq : ν * (R ^ 2 / ϱ y ^ 2) = ν * R ^ 2 / ϱ y ^ 2 := by ring
  have hL : 0 < R * Real.sqrt ν := mul_pos hR (Real.sqrt_pos.2 hν)
  have hU : 0 < R * Real.sqrt (5 * ν / 4) := mul_pos hR (Real.sqrt_pos.2 (by positivity))
  have e1 : (R * Real.sqrt ν) ^ 2 = ν * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hν.le]; ring
  have e2 : (R * Real.sqrt (5 * ν / 4)) ^ 2 = 5 * ν * R ^ 2 / 4 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have c1 : ϱ y < R * Real.sqrt ν ↔ ϱ y ^ 2 < ν * R ^ 2 := by
    rw [← sq_lt_sq₀ hy.le hL.le, e1]
  have c2 : R * Real.sqrt (5 * ν / 4) < ϱ y ↔ 5 * ν * R ^ 2 / 4 < ϱ y ^ 2 := by
    rw [← sq_lt_sq₀ hU.le hy.le, e2]
  unfold tcOut streamAnn
  simp only [mem_setOf_eq, not_and_or, not_le]
  rw [hq, c1, c2, div_lt_iff₀ hρ2, lt_div_iff₀ hρ2]
  constructor
  · rintro (h | h)
    · right; nlinarith
    · left; nlinarith
  · rintro (h | h)
    · right; nlinarith
    · left; nlinarith

theorem age_eq (R : ℝ) (y : Space) : age R y = R ^ 2 / ϱ y ^ 2 := rfl

theorem sepComm_eq_tcComm_out {ν μ R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) {y : Space} (hy : 0 < ϱ y)
    (h : tcOut ν R (ϱ y)) : sepComm ν μ R χy T τ y = 0 := by
  have hev : ∀ᶠ y' in 𝓝 y, tcOut ν R (ϱ y') :=
    (continuous_ϱ.continuousAt).eventually (tcOut_eventually hy.ne' h)
  unfold sepComm
  rcases h with h | h
  · -- young region: the cut is the identity
    have hev' : ∀ᶠ y' in 𝓝 y, ν * age R y' < 4 / 5 := by
      have hc : ContinuousAt (fun y' : Space => ν * (R ^ 2 / ϱ y' ^ 2)) y :=
        (continuousAt_const.div ((continuous_ϱ.pow 2).continuousAt) (pow_ne_zero 2 hy.ne')).const_mul ν
      exact hc.eventually_lt continuousAt_const h
    have hX : ∀ t, sepWX ν μ R χy T t =ᶠ[𝓝 y] sepX0 ν μ T t := fun t => by
      filter_upwards [hev'] with y' hy'
      exact wardStreamCut_eq_self_young hχ _ t hy'
    rw [physDmu_congr_local hX, wardStreamCut_eq_self_young hχ _ τ (by simpa [age_eq] using h)]
    simp
  · have hev' : ∀ᶠ y' in 𝓝 y, 1 < ν * age R y' := by
      have hc : ContinuousAt (fun y' : Space => ν * (R ^ 2 / ϱ y' ^ 2)) y :=
        (continuousAt_const.div ((continuous_ϱ.pow 2).continuousAt) (pow_ne_zero 2 hy.ne')).const_mul ν
      exact continuousAt_const.eventually_lt hc h
    have hX : ∀ t, sepWX ν μ R χy T t =ᶠ[𝓝 y] (fun _ => (0 : Space)) := fun t => by
      filter_upwards [hev'] with y' hy'
      exact wardStreamCut_eq_zero_old hχ _ t hy'
    have := physDmu_congr_local (ν := ν) (m := μ + 1) (τ := τ) hX
    rw [this, physDmu_zero, wardStreamCut_eq_zero_old hχ _ τ (by simpa [age_eq] using h)]
    simp

theorem tcComm_eq_zero_out {ν R : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (Z : ℝ → Space → Space) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) (h : tcOut ν R (ϱ y)) :
    tcComm ν R χy Z τ y = 0 := by
  obtain ⟨a1, a2, b1, b2⟩ := tc_coeff_zero hχ hy.ne' h
  simp [tcComm, a1, a2, b1, b2]

/-- On the annulus, the leaves of `TransCommPoint` identify the commutator. -/
theorem sepComm_eq_tcComm {σ₁ σ₂ ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hσ : -(1 / 4) < σ₁) (hν : 0 < ν) (hν1 : ν ≤ 1) (hR1 : 1 ≤ R) (hP : 0 < P)
    (hμ : μ ∈ Icc σ₁ σ₂) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    sepComm ν μ R χy T τ y = tcComm ν R χy (sepX0 ν μ T) τ y := by
  have hR : 0 < R := by linarith
  by_cases hmem : y ∈ streamAnn ν R
  · have hctx : TCCtx σ₁ σ₂ ν μ R P T y := ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hmem⟩
    obtain ⟨r1, r2, r3, r4⟩ := tcReg σ₁ σ₂ ν μ R P T τ y hctx
    obtain ⟨i1, i2, i3, i4⟩ := tcInt σ₁ σ₂ ν μ R P T τ y hctx
    exact tcLeibniz ν μ R χy hχ hν hR (sepX0 ν μ T) τ y hy r1 r2 r3 r4 i1 i2 i3 i4
      (tcTime σ₁ σ₂ ν μ R P T τ y hctx) (tcGrad σ₁ σ₂ ν μ R P T τ y hctx)
      (tcLap σ₁ σ₂ ν μ R P T τ y hctx) (tcRad σ₁ σ₂ ν μ R P T τ y hctx) (μ + 1)
  · have hout := (tcOut_iff_not_mem hν hR hy).2 hmem
    rw [sepComm_eq_tcComm_out hχ T τ hy hout, tcComm_eq_zero_out hχ _ τ hy hout]

/-- The commutator `YB` of a separated source is differentiable off the axis. -/
theorem sepComm_diffAt {σ₁ σ₂ ν μ R P : ℝ} {χy : ℝ → ℝ} (hχ : IsStreamCutoff χy)
    (hσ : -(1 / 4) < σ₁) (hν : 0 < ν) (hν1 : ν ≤ 1) (hR1 : 1 ≤ R) (hP : 0 < P)
    (hμ : μ ∈ Icc σ₁ σ₂) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hM : SepMoment P T)
    (hA : IsAxiSource T) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ (sepComm ν μ R χy T τ) y := by
  have hR : 0 < R := by linarith
  have hpos : ∀ᶠ y' in 𝓝 y, 0 < ϱ y' := (continuous_ϱ.continuousAt).eventually (lt_mem_nhds hy)
  have heq : sepComm ν μ R χy T τ =ᶠ[𝓝 y] tcComm ν R χy (sepX0 ν μ T) τ := by
    filter_upwards [hpos] with y' hy'
    exact sepComm_eq_tcComm hχ hσ hν hν1 hR1 hP hμ hT hM hA τ hy'
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  by_cases hmem : y ∈ streamAnn ν R
  · have hctx : TCCtx σ₁ σ₂ ν μ R P T y := ⟨hσ, hν, hν1, hR1, hP, hμ, hT, hM, hA, hmem⟩
    obtain ⟨r1, r2, r3, r4⟩ := tcReg σ₁ σ₂ ν μ R P T τ y hctx
    exact tcComm_diffAt hχ (sepX0 ν μ T) τ hy r1 r3
  · have hout := (tcOut_iff_not_mem hν hR hy).2 hmem
    have hz := tcComm_eventually_zero hχ (sepX0 ν μ T) τ hy hout
    exact (differentiableAt_const (0 : Space)).congr_of_eventuallyEq hz

end UnforcedLeray.Short.PartIIIb.Concrete.Sub8_1_1_2_3
