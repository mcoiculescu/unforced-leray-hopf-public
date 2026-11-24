import UnforcedLeray.Short.PartIIa.StatementsRing
import UnforcedLeray.Short.PartIIa.Tasks.R03ResidualChart
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Helper module `ProfileDerivs` for `PartII-a:R05`

Off-axis representation, smoothness, and first-derivative formulas for the five chart terms
of `ringResidual R ν ψ pr τ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.R05

open UnforcedLeray.RingLift UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187
  UnforcedLeray.B0188 UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa

/-! ### 1. Smoothness of profile operators and residual coefficients on `ageDomain` -/

theorem isOpen_ageDomain' : IsOpen ageDomain :=
  isOpen_lt continuous_const (continuous_snd.comp continuous_snd)

theorem contDiffOn_fderiv_dir {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain)
    (v : ProfilePoint) : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) ageDomain :=
  (hf.fderiv_of_isOpen isOpen_ageDomain' (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_partialQ {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (partialQ f) ageDomain :=
  contDiffOn_fderiv_dir hf eqDir

theorem contDiffOn_partialEta {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (partialEta f) ageDomain :=
  contDiffOn_fderiv_dir hf eηDir

theorem contDiffOn_partialAge {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (partialAge f) ageDomain :=
  contDiffOn_fderiv_dir hf esDir

theorem contDiffOn_ageOperator {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (ageOperator f) ageDomain := by
  have hc1 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => x.2.1) ageDomain :=
    (show ContDiff ℝ ∞ (fun x : ProfilePoint => x.2.1) by fun_prop).contDiffOn
  have hc2 : ContDiffOn ℝ ∞ (fun x : ProfilePoint => 2 * x.2.2) ageDomain :=
    (show ContDiff ℝ ∞ (fun x : ProfilePoint => 2 * x.2.2) by fun_prop).contDiffOn
  exact (hc1.mul (contDiffOn_partialEta hf)).add (hc2.mul (contDiffOn_partialAge hf))

theorem contDiffOn_ageShift (a : ℝ) {f : ProfilePoint → ℝ} (hf : ContDiffOn ℝ ∞ f ageDomain) :
    ContDiffOn ℝ ∞ (ageShift a f) ageDomain :=
  (contDiffOn_ageOperator hf).add (contDiffOn_const.mul hf)

theorem contDiffOn_streamV1 {ψ : ProfilePoint → ℝ} (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (streamV1 ψ) ageDomain :=
  (contDiffOn_partialEta hψ).neg

theorem contDiffOn_streamV2 {ψ : ProfilePoint → ℝ} (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (streamV2 ψ) ageDomain :=
  contDiffOn_partialQ hψ

theorem contDiffOn_ageDefect {ψ : ProfilePoint → ℝ} (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (ageDefect ψ) ageDomain :=
  hψ.sub (contDiffOn_ageOperator hψ)

theorem contDiffOn_profileLap {g : ProfilePoint → ℝ} (hg : ContDiffOn ℝ ∞ g ageDomain) :
    ContDiffOn ℝ ∞ (profileLap g) ageDomain :=
  (contDiffOn_partialQ (contDiffOn_partialQ hg)).add
    (contDiffOn_partialEta (contDiffOn_partialEta hg))

theorem contDiffOn_transportDiffusion (ν : ℝ) {ψ g : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ ageDomain) (hg : ContDiffOn ℝ ∞ g ageDomain) :
    ContDiffOn ℝ ∞ (transportDiffusion ν ψ g) ageDomain :=
  (((contDiffOn_partialAge hg).add ((contDiffOn_streamV1 hψ).mul (contDiffOn_partialQ hg))).add
    ((contDiffOn_streamV2 hψ).mul (contDiffOn_partialEta hg))).sub
      (contDiffOn_const.mul (contDiffOn_profileLap hg))

theorem contDiffOn_coeffA1 (ν : ℝ) {ψ p : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ ageDomain) (hp : ContDiffOn ℝ ∞ p ageDomain) :
    ContDiffOn ℝ ∞ (coeffA₁ ν ψ p) ageDomain := by
  have hv1 := contDiffOn_streamV1 hψ
  have hH := contDiffOn_ageDefect hψ
  exact (((((hv1.mul (contDiffOn_ageOperator hv1)).neg).add
    (hH.mul (contDiffOn_partialEta hv1))).sub (hv1.pow 2)).add
      (contDiffOn_const.mul (contDiffOn_ageShift 1 (contDiffOn_partialQ hv1)))).sub
        (contDiffOn_ageShift 2 hp)

theorem contDiffOn_coeffA2 (ν : ℝ) {ψ : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (coeffA₂ ν ψ) ageDomain := by
  have hv1 := contDiffOn_streamV1 hψ
  have hv2 := contDiffOn_streamV2 hψ
  have hH := contDiffOn_ageDefect hψ
  exact (((contDiffOn_transportDiffusion ν hψ hH).add
    (hH.mul (contDiffOn_partialEta hv2))).sub
      (hv1.mul (contDiffOn_ageShift 1 hv2))).add
        (contDiffOn_const.mul (contDiffOn_ageShift 1 (contDiffOn_partialQ hv2)))

theorem contDiffOn_coeffB1 (ν : ℝ) {ψ : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (coeffB₁ ν ψ) ageDomain :=
  contDiffOn_const.mul (contDiffOn_ageOperator (contDiffOn_ageShift 2 (contDiffOn_streamV1 hψ)))

theorem contDiffOn_coeffB2 (ν : ℝ) {ψ : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (coeffB₂ ν ψ) ageDomain := by
  have hv1 := contDiffOn_streamV1 hψ
  have hv2 := contDiffOn_streamV2 hψ
  have hH := contDiffOn_ageDefect hψ
  exact ((((hv1.mul (contDiffOn_ageShift 1 hH)).neg).add
    (hH.mul (contDiffOn_partialEta hH))).add
      (contDiffOn_const.mul (contDiffOn_ageShift 1 (contDiffOn_partialQ hH)))).sub
        (contDiffOn_const.mul (contDiffOn_ageShift 1 (contDiffOn_ageShift 1 hv2)))

theorem contDiffOn_coeffB3 (ν : ℝ) {ψ : ProfilePoint → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ ageDomain) :
    ContDiffOn ℝ ∞ (coeffB₃ ν ψ) ageDomain :=
  contDiffOn_const.mul (contDiffOn_ageShift 1 (contDiffOn_ageShift 1 (contDiffOn_ageDefect hψ)))

/-! ### 2. Consequences of `IsExactPlanarTrain` -/

theorem exactTrain_smooth {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) {ψ pr : ProfilePoint → ℝ}
    (htr : IsExactPlanarTrain ν c ψ pr) :
    ContDiffOn ℝ ∞ ψ ageDomain ∧ ContDiffOn ℝ ∞ pr ageDomain := by
  rcases htr with ⟨T, hBUC, rfl, rfl⟩
  exact lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth ν c hν hc T hBUC

theorem exactTrain_periodic {ν c : ℝ} {ψ pr : ProfilePoint → ℝ}
    (htr : IsExactPlanarTrain ν c ψ pr) :
    QPeriodicOn c ψ ∧ QPeriodicOn c pr := by
  rcases htr with ⟨T, _, rfl, rfl⟩
  exact ⟨qPeriodicOn_trainStream T, qPeriodicOn_trainPressure T⟩

theorem exactTrain_residual_polynomial (R : ℝ) {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr)
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    chartRadialResidual R ν (streamV1 ψ) (axialProfile R ψ) pr x =
        ringEps R * coeffA₁ ν ψ pr x + ringEps R ^ 2 * coeffB₁ ν ψ x ∧
      chartAxialResidual R ν (streamV1 ψ) (axialProfile R ψ) pr x =
        ringEps R * coeffA₂ ν ψ x + ringEps R ^ 2 * coeffB₂ ν ψ x +
          ringEps R ^ 3 * coeffB₃ ν ψ x := by
  have hsm := (exactTrain_smooth hν hc htr).1
  rcases htr with ⟨T, _, rfl, rfl⟩
  have hC3 : TrainStreamC3 T.ψ := hsm.of_le (by simp)
  exact train_residual_polynomial R T.isTrain hC3 hx

/-! ### 3. The 5-term chart decomposition off the axis -/

/-- Scalar chart lift `s(y)^{3/2} X(q, η, s)`. -/
def chartVal (R τ : ℝ) (X : ProfilePoint → ℝ) (y : Space) : ℝ :=
  (Axi.age R y) ^ (3 / 2 : ℝ) * X (chartPtR03 R τ y)

/-- Radial chart lift `s(y)^{3/2} X(q, η, s) e_r(y)`. -/
def radLift (R : ℝ) (X : ProfilePoint → ℝ) (τ : ℝ) (y : Space) : Space :=
  chartVal R τ X y • Axi.eR y

/-- Axial chart lift `s(y)^{3/2} X(q, η, s) e_3`. -/
def axLift (R : ℝ) (X : ProfilePoint → ℝ) (τ : ℝ) (y : Space) : Space :=
  chartVal R τ X y • Axi.e3

/-- The 5-term expansion of `ringResidual R ν ψ pr τ y` off the axis. -/
def resFiveTerms (R ν : ℝ) (ψ pr : ProfilePoint → ℝ) (τ : ℝ) (y : Space) : Space :=
  ringEps R • radLift R (coeffA₁ ν ψ pr) τ y +
    (ringEps R ^ 2) • radLift R (coeffB₁ ν ψ) τ y +
    ringEps R • axLift R (coeffA₂ ν ψ) τ y +
    (ringEps R ^ 2) • axLift R (coeffB₂ ν ψ) τ y +
    (ringEps R ^ 3) • axLift R (coeffB₃ ν ψ) τ y

theorem ringResidual_eq_resFiveTerms {R ν c : ℝ} (hR : 2 ≤ R) (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr) (τ : ℝ) {y : Space}
    (hy : y ∉ Axi.axis) :
    ringResidual R ν ψ pr τ y = resFiveTerms R ν ψ pr τ y := by
  have hR0 : R ≠ 0 := by linarith
  have hϱ : Axi.ϱ y ≠ 0 := Axi.ϱ_ne_zero hy
  have hs : 0 < (chartPtR03 R τ y).2.2 := Axi.age_pos hR0 hy
  obtain ⟨hψ, hpr⟩ := exactTrain_smooth hν hc htr
  have hψ3 : ContDiffAt ℝ 3 ψ (chartPtR03 R τ y) :=
    (hψ.contDiffAt (isOpen_ageDomain'.mem_nhds hs)).of_le (by norm_num)
  have hpr1 : ContDiffAt ℝ 1 pr (chartPtR03 R τ y) :=
    (hpr.contDiffAt (isOpen_ageDomain'.mem_nhds hs)).of_le (by norm_num)
  rw [ringResidual_eq_chart R ν hR ψ pr τ y hϱ hψ3 hpr1]
  obtain ⟨hrad, hax⟩ := exactTrain_residual_polynomial R hν hc htr hs
  rw [hrad, hax]
  simp only [resFiveTerms, radLift, axLift, chartVal]
  module

/-! ### 4. Off-axis smoothness and first derivatives of `chartVal`, `radLift`, `axLift` -/

/-- Derivative of `chartPtR03 R τ` at `y`. -/
def chartPtD (R : ℝ) (y : Space) : Space →L[ℝ] ProfilePoint :=
  (Axi.phaseD R y).prod ((Axi.transD R y).prod (Axi.ageD R y))

theorem chartPtD_apply (R : ℝ) (y v : Space) :
    chartPtD R y v =
      (R / Axi.ϱ y * Axi.ϱD y v,
        (R / Axi.ϱ y * v 2 - R * y 2 / Axi.ϱ y ^ 2 * Axi.ϱD y v,
          -(2 * R ^ 2 / Axi.ϱ y ^ 3) * Axi.ϱD y v)) := by
  simp only [chartPtD, Axi.phaseD, Axi.transD, Axi.ageD, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
    EuclideanSpace.coe_proj]

theorem hasFDerivAt_chartPtR03 {R : ℝ} (hR : R ≠ 0) (τ : ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    HasFDerivAt (chartPtR03 R τ) (chartPtD R y) y :=
  (Axi.hasFDerivAt_phase hR τ hy).prodMk
    ((Axi.hasFDerivAt_trans R hy).prodMk (Axi.hasFDerivAt_age R hy))

theorem contDiffOn_chartPtR03 {R : ℝ} (hR : 0 < R) (τ : ℝ) :
    ContDiffOn ℝ ∞ (chartPtR03 R τ) Axi.axisᶜ := by
  have hϱ : ContDiffOn ℝ ∞ Axi.ϱ Axi.axisᶜ := Axi.contDiffOn_ϱ
  have hAge : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ :=
    contDiffOn_const.div (hϱ.pow 2) (fun _ hy => pow_ne_zero 2 (Axi.ϱ_ne_zero hy))
  have hLog : ContDiffOn ℝ ∞ (fun y => Real.log (Axi.age R y)) Axi.axisᶜ :=
    hAge.log (fun _ hy => (Axi.age_pos hR.ne' hy).ne')
  have hPhase : ContDiffOn ℝ ∞ (Axi.phase R τ) Axi.axisᶜ :=
    contDiffOn_const.sub (contDiffOn_const.mul hLog)
  have h2 : ContDiffOn ℝ ∞ (fun y : Space => R * y 2) Axi.axisᶜ :=
    (show ContDiff ℝ ∞ (fun y : Space => R * y 2) by fun_prop).contDiffOn
  have hTrans : ContDiffOn ℝ ∞ (Axi.trans R) Axi.axisᶜ :=
    h2.div hϱ (fun _ hy => Axi.ϱ_ne_zero hy)
  exact hPhase.prodMk (hTrans.prodMk hAge)

theorem mapsTo_chartPtR03 {R : ℝ} (hR : 0 < R) (τ : ℝ) :
    MapsTo (chartPtR03 R τ) Axi.axisᶜ ageDomain :=
  fun _ hy => Axi.age_pos hR.ne' hy

theorem contDiffOn_chartVal {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) :
    ContDiffOn ℝ ∞ (chartVal R τ X) Axi.axisᶜ := by
  have hAge : ContDiffOn ℝ ∞ (Axi.age R) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2) (fun _ hy => pow_ne_zero 2 (Axi.ϱ_ne_zero hy))
  have hPow : ContDiffOn ℝ ∞ (fun y => (Axi.age R y) ^ (3 / 2 : ℝ)) Axi.axisᶜ :=
    hAge.rpow_const_of_ne (fun _ hy => (Axi.age_pos hR.ne' hy).ne')
  have hComp : ContDiffOn ℝ ∞ (fun y => X (chartPtR03 R τ y)) Axi.axisᶜ :=
    hX.comp (contDiffOn_chartPtR03 hR τ) (mapsTo_chartPtR03 hR τ)
  exact hPow.mul hComp

theorem contDiffOn_radLift {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) :
    ContDiffOn ℝ ∞ (radLift R X τ) Axi.axisᶜ :=
  (contDiffOn_chartVal hR τ hX).smul Axi.contDiffOn_eR

theorem contDiffOn_axLift {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) :
    ContDiffOn ℝ ∞ (axLift R X τ) Axi.axisᶜ :=
  (contDiffOn_chartVal hR τ hX).smul contDiffOn_const

theorem contDiffOn_resFiveTerms {R ν c : ℝ} (hR : 0 < R) (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr) (τ : ℝ) :
    ContDiffOn ℝ ∞ (resFiveTerms R ν ψ pr τ) Axi.axisᶜ := by
  obtain ⟨hψ, hpr⟩ := exactTrain_smooth hν hc htr
  have hA1 := contDiffOn_radLift hR τ (contDiffOn_coeffA1 ν hψ hpr)
  have hB1 := contDiffOn_radLift hR τ (contDiffOn_coeffB1 ν hψ)
  have hA2 := contDiffOn_axLift hR τ (contDiffOn_coeffA2 ν hψ)
  have hB2 := contDiffOn_axLift hR τ (contDiffOn_coeffB2 ν hψ)
  have hB3 := contDiffOn_axLift hR τ (contDiffOn_coeffB3 ν hψ)
  exact ((((hA1.const_smul (ringEps R)).add (hB1.const_smul (ringEps R ^ 2))).add
    (hA2.const_smul (ringEps R))).add (hB2.const_smul (ringEps R ^ 2))).add
      (hB3.const_smul (ringEps R ^ 3))

theorem contDiffOn_ringResidual {R ν c : ℝ} (hR : 2 ≤ R) (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr) (τ : ℝ) :
    ContDiffOn ℝ 1 (ringResidual R ν ψ pr τ) Axi.axisᶜ := by
  have hR0 : 0 < R := by linarith
  have h5 : ContDiffOn ℝ 1 (resFiveTerms R ν ψ pr τ) Axi.axisᶜ :=
    (contDiffOn_resFiveTerms hR0 hν hc htr τ).of_le (by simp)
  exact h5.congr (fun y hy => ringResidual_eq_resFiveTerms hR hν hc htr τ hy)

/-- Scalar directional derivative of `chartVal R τ X` at `y ∉ Axi.axis` along `v`. -/
def chartValDeriv (R τ : ℝ) (X : ProfilePoint → ℝ) (y v : Space) : ℝ :=
  (Axi.age R y) ^ 2 *
    (Axi.ϱD y v * (partialQ X (chartPtR03 R τ y) - R⁻¹ * ageShift 3 X (chartPtR03 R τ y)) +
      v 2 * partialEta X (chartPtR03 R τ y))

theorem age_rpow_half {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ Axi.axis) :
    (Axi.age R y) ^ ((3 / 2 : ℝ) - 1) = R / Axi.ϱ y := by
  have h1 : (3 / 2 : ℝ) - 1 = 1 / 2 := by ring
  rw [h1, ← Real.sqrt_eq_rpow, Axi.sqrt_age hR hy]

theorem age_rpow_three_halves_eq {R : ℝ} (hR : 0 < R) {y : Space} (hy : y ∉ Axi.axis) :
    (Axi.age R y) ^ (3 / 2 : ℝ) = (R / Axi.ϱ y) ^ 3 := by
  have hpos : 0 ≤ R / Axi.ϱ y := (div_pos hR (Axi.ϱ_pos hy)).le
  have hA : Axi.age R y = (R / Axi.ϱ y) ^ (2 : ℝ) := by
    unfold Axi.age
    rw [Real.rpow_two, div_pow]
  rw [hA, ← Real.rpow_mul hpos, show (2 : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

theorem fderiv_chartVal_apply {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) (v : Space) :
    fderiv ℝ (chartVal R τ X) y v = chartValDeriv R τ X y v := by
  have hR0 : R ≠ 0 := hR.ne'
  have hρ0 : Axi.ϱ y ≠ 0 := Axi.ϱ_ne_zero hy
  have hs : 0 < Axi.age R y := Axi.age_pos hR0 hy
  have hPow : HasFDerivAt (fun z => (Axi.age R z) ^ (3 / 2 : ℝ))
      (((3 / 2 : ℝ) * (Axi.age R y) ^ ((3 / 2 : ℝ) - 1)) • Axi.ageD R y) y :=
    (Real.hasDerivAt_rpow_const (Or.inl hs.ne')).comp_hasFDerivAt y (Axi.hasFDerivAt_age R hy)
  have hXd : DifferentiableAt ℝ X (chartPtR03 R τ y) :=
    (hX.contDiffAt (isOpen_ageDomain'.mem_nhds hs)).differentiableAt (by simp)
  have hComp : HasFDerivAt (fun z => X (chartPtR03 R τ z))
      ((fderiv ℝ X (chartPtR03 R τ y)).comp (chartPtD R y)) y :=
    hXd.hasFDerivAt.comp y (hasFDerivAt_chartPtR03 hR0 τ hy)
  have hMul : HasFDerivAt (chartVal R τ X) _ y := hPow.mul hComp
  have hApp := congrArg (fun L : Space →L[ℝ] ℝ => L v) hMul.fderiv
  rw [hApp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, Axi.ageD]
  rw [chartPtD_apply, clm_apply_coords (fderiv ℝ X (chartPtR03 R τ y)),
    age_rpow_half hR hy, age_rpow_three_halves_eq hR hy]
  simp only [chartValDeriv, ageShift, ageOperator, partialQ, partialEta, partialAge,
    chartPtR03, Axi.age, Axi.trans]
  field_simp
  ring

theorem hasFDerivAt_radLift {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) :
    DifferentiableAt ℝ (radLift R X τ) y ∧
      ∀ v : Space, fderiv ℝ (radLift R X τ) y v =
        chartValDeriv R τ X y v • Axi.eR y +
          (R⁻¹ * (Axi.age R y) ^ 2 * X (chartPtR03 R τ y)) •
            (Axi.hor v - Axi.ϱD y v • Axi.eR y) := by
  have hCV : DifferentiableAt ℝ (chartVal R τ X) y :=
    ((contDiffOn_chartVal hR τ hX).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).differentiableAt
      (by simp)
  have hF : HasFDerivAt (radLift R X τ) _ y := hCV.hasFDerivAt.smul (Axi.hasFDerivAt_eR hy)
  refine ⟨hF.differentiableAt, fun v => ?_⟩
  have hApp := congrArg (fun L : Space →L[ℝ] Space => L v) hF.fderiv
  rw [hApp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  have hR0 : R ≠ 0 := hR.ne'
  have hρ0 : Axi.ϱ y ≠ 0 := Axi.ϱ_ne_zero hy
  have hsc : chartVal R τ X y * (Axi.ϱ y)⁻¹ = R⁻¹ * (Axi.age R y) ^ 2 * X (chartPtR03 R τ y) := by
    unfold chartVal
    rw [age_rpow_three_halves_eq hR hy]
    unfold Axi.age
    field_simp
  rw [fderiv_chartVal_apply hR τ hX hy v, Axi.eRD_apply, smul_smul, hsc, add_comm]

theorem hasFDerivAt_axLift {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) :
    DifferentiableAt ℝ (axLift R X τ) y ∧
      ∀ v : Space, fderiv ℝ (axLift R X τ) y v = chartValDeriv R τ X y v • Axi.e3 := by
  have hCV : DifferentiableAt ℝ (chartVal R τ X) y :=
    ((contDiffOn_chartVal hR τ hX).contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).differentiableAt
      (by simp)
  have hF : HasFDerivAt (axLift R X τ) _ y := hCV.hasFDerivAt.smul (hasFDerivAt_const Axi.e3 y)
  refine ⟨hF.differentiableAt, fun v => ?_⟩
  have hApp := congrArg (fun L : Space →L[ℝ] Space => L v) hF.fderiv
  rw [hApp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.smulRight_apply, smul_zero, zero_add]
  rw [fderiv_chartVal_apply hR τ hX hy v]

/-! ### 5. Pointwise norm bounds on `radLift`, `axLift`, and their derivatives -/

theorem norm_hor_le (v : Space) : ‖Axi.hor v‖ ≤ ‖v‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Axi.hor_apply_zero, Axi.hor_apply_one, Axi.hor_apply_two]
  linarith [sq_nonneg (v 2)]

theorem abs_ϱD_le {y : Space} (hy : y ∉ Axi.axis) (v : Space) : |Axi.ϱD y v| ≤ ‖v‖ := by
  have heq : Axi.ϱD y v = inner ℝ (Axi.eR y) v := by
    rw [Axi.ϱD_apply]
    simp only [PiLp.inner_apply, Fin.sum_univ_three, Axi.eR_apply_zero, Axi.eR_apply_one,
      Axi.eR_apply_two, RCLike.inner_apply, conj_trivial]
    ring
  rw [heq, ← Real.norm_eq_abs]
  calc ‖inner ℝ (Axi.eR y) v‖ ≤ ‖Axi.eR y‖ * ‖v‖ := norm_inner_le_norm _ _
    _ = 1 * ‖v‖ := by rw [Axi.norm_eR hy]
    _ = ‖v‖ := one_mul _

theorem abs_coord_two_le (v : Space) : |v 2| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le v 2

theorem norm_e3 : ‖Axi.e3‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  simp [Axi.e3_apply]

theorem norm_radLift_le (R τ : ℝ) (X : ProfilePoint → ℝ) {y : Space} (hy : y ∉ Axi.axis) :
    ‖radLift R X τ y‖ ≤ (Axi.age R y) ^ (3 / 2 : ℝ) * |X (chartPtR03 R τ y)| := by
  unfold radLift chartVal
  rw [norm_smul, Axi.norm_eR hy, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by unfold Axi.age; positivity) _)]

theorem norm_axLift_le (R τ : ℝ) (X : ProfilePoint → ℝ) (y : Space) :
    ‖axLift R X τ y‖ ≤ (Axi.age R y) ^ (3 / 2 : ℝ) * |X (chartPtR03 R τ y)| := by
  unfold axLift chartVal
  rw [norm_smul, norm_e3, mul_one, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by unfold Axi.age; positivity) _)]

theorem abs_chartValDeriv_le {R : ℝ} (hR : 0 < R) (τ : ℝ) (X : ProfilePoint → ℝ)
    {y : Space} (hy : y ∉ Axi.axis) {v : Space} (hv : ‖v‖ ≤ 1) :
    |chartValDeriv R τ X y v| ≤
      (Axi.age R y) ^ 2 *
        (|partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
          |partialEta X (chartPtR03 R τ y)|) := by
  have hs2 : 0 ≤ (Axi.age R y) ^ 2 := sq_nonneg _
  have h1 : |Axi.ϱD y v| ≤ 1 := (abs_ϱD_le hy v).trans hv
  have h2 : |v 2| ≤ 1 := (abs_coord_two_le v).trans hv
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  unfold chartValDeriv
  rw [abs_mul, abs_of_nonneg hs2]
  gcongr
  calc |Axi.ϱD y v * (partialQ X (chartPtR03 R τ y) - R⁻¹ * ageShift 3 X (chartPtR03 R τ y)) +
          v 2 * partialEta X (chartPtR03 R τ y)|
      ≤ |Axi.ϱD y v * (partialQ X (chartPtR03 R τ y) - R⁻¹ * ageShift 3 X (chartPtR03 R τ y))| +
          |v 2 * partialEta X (chartPtR03 R τ y)| := abs_add_le _ _
    _ = |Axi.ϱD y v| * |partialQ X (chartPtR03 R τ y) - R⁻¹ * ageShift 3 X (chartPtR03 R τ y)| +
          |v 2| * |partialEta X (chartPtR03 R τ y)| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (|partialQ X (chartPtR03 R τ y)| + |R⁻¹ * ageShift 3 X (chartPtR03 R τ y)|) +
          1 * |partialEta X (chartPtR03 R τ y)| := by
        gcongr
        exact abs_sub _ _
    _ = |partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
          |partialEta X (chartPtR03 R τ y)| := by
        rw [abs_mul, abs_of_nonneg hRinv]
        ring

theorem norm_fderiv_radLift_le {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis)
    {v : Space} (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (radLift R X τ) y v‖ ≤
      (Axi.age R y) ^ 2 *
        (|partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
          |partialEta X (chartPtR03 R τ y)| + 2 * R⁻¹ * |X (chartPtR03 R τ y)|) := by
  rw [(hasFDerivAt_radLift hR τ hX hy).2 v]
  have hs2 : 0 ≤ (Axi.age R y) ^ 2 := sq_nonneg _
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  have hhor : ‖Axi.hor v - Axi.ϱD y v • Axi.eR y‖ ≤ 2 := by
    calc ‖Axi.hor v - Axi.ϱD y v • Axi.eR y‖
        ≤ ‖Axi.hor v‖ + ‖Axi.ϱD y v • Axi.eR y‖ := norm_sub_le _ _
      _ = ‖Axi.hor v‖ + |Axi.ϱD y v| * ‖Axi.eR y‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 + 1 * 1 := by
        rw [Axi.norm_eR hy]
        linarith [(norm_hor_le v).trans hv, (abs_ϱD_le hy v).trans hv]
      _ = 2 := by ring
  calc ‖chartValDeriv R τ X y v • Axi.eR y +
          (R⁻¹ * (Axi.age R y) ^ 2 * X (chartPtR03 R τ y)) •
            (Axi.hor v - Axi.ϱD y v • Axi.eR y)‖
      ≤ ‖chartValDeriv R τ X y v • Axi.eR y‖ +
          ‖(R⁻¹ * (Axi.age R y) ^ 2 * X (chartPtR03 R τ y)) •
            (Axi.hor v - Axi.ϱD y v • Axi.eR y)‖ := norm_add_le _ _
    _ = |chartValDeriv R τ X y v| * 1 +
          (R⁻¹ * (Axi.age R y) ^ 2 * |X (chartPtR03 R τ y)|) *
            ‖Axi.hor v - Axi.ϱD y v • Axi.eR y‖ := by
        rw [norm_smul, Axi.norm_eR hy, Real.norm_eq_abs, norm_smul, Real.norm_eq_abs,
          abs_mul, abs_mul, abs_of_nonneg hRinv, abs_of_nonneg hs2]
    _ ≤ (Axi.age R y) ^ 2 *
          (|partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
            |partialEta X (chartPtR03 R τ y)|) * 1 +
          (R⁻¹ * (Axi.age R y) ^ 2 * |X (chartPtR03 R τ y)|) * 2 := by
        gcongr
        exact abs_chartValDeriv_le hR τ X hy hv
    _ = (Axi.age R y) ^ 2 *
          (|partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
            |partialEta X (chartPtR03 R τ y)| + 2 * R⁻¹ * |X (chartPtR03 R τ y)|) := by
        ring

theorem norm_fderiv_axLift_le {R : ℝ} (hR : 0 < R) (τ : ℝ) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis)
    {v : Space} (hv : ‖v‖ ≤ 1) :
    ‖fderiv ℝ (axLift R X τ) y v‖ ≤
      (Axi.age R y) ^ 2 *
        (|partialQ X (chartPtR03 R τ y)| + R⁻¹ * |ageShift 3 X (chartPtR03 R τ y)| +
          |partialEta X (chartPtR03 R τ y)|) := by
  rw [(hasFDerivAt_axLift hR τ hX hy).2 v, norm_smul, norm_e3, mul_one, Real.norm_eq_abs]
  exact abs_chartValDeriv_le hR τ X hy hv

theorem fderiv_ringResidual_eq_resFiveTerms {R ν c : ℝ} (hR : 2 ≤ R) (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr) (τ : ℝ) {y : Space}
    (hy : y ∉ Axi.axis) (v : Space) :
    fderiv ℝ (ringResidual R ν ψ pr τ) y v =
      ringEps R • fderiv ℝ (radLift R (coeffA₁ ν ψ pr) τ) y v +
        (ringEps R ^ 2) • fderiv ℝ (radLift R (coeffB₁ ν ψ) τ) y v +
        ringEps R • fderiv ℝ (axLift R (coeffA₂ ν ψ) τ) y v +
        (ringEps R ^ 2) • fderiv ℝ (axLift R (coeffB₂ ν ψ) τ) y v +
        (ringEps R ^ 3) • fderiv ℝ (axLift R (coeffB₃ ν ψ) τ) y v := by
  have hR0 : 0 < R := by linarith
  have hev : ringResidual R ν ψ pr τ =ᶠ[𝓝 y] resFiveTerms R ν ψ pr τ := by
    filter_upwards [Axi.isOpen_compl_axis.mem_nhds hy] with z hz
    exact ringResidual_eq_resFiveTerms hR hν hc htr τ hz
  rw [hev.fderiv_eq]
  obtain ⟨hψ, hpr⟩ := exactTrain_smooth hν hc htr
  have dA1 := ((hasFDerivAt_radLift hR0 τ (contDiffOn_coeffA1 ν hψ hpr) hy).1.hasFDerivAt).const_smul
    (ringEps R)
  have dB1 := ((hasFDerivAt_radLift hR0 τ (contDiffOn_coeffB1 ν hψ) hy).1.hasFDerivAt).const_smul
    (ringEps R ^ 2)
  have dA2 := ((hasFDerivAt_axLift hR0 τ (contDiffOn_coeffA2 ν hψ) hy).1.hasFDerivAt).const_smul
    (ringEps R)
  have dB2 := ((hasFDerivAt_axLift hR0 τ (contDiffOn_coeffB2 ν hψ) hy).1.hasFDerivAt).const_smul
    (ringEps R ^ 2)
  have dB3 := ((hasFDerivAt_axLift hR0 τ (contDiffOn_coeffB3 ν hψ) hy).1.hasFDerivAt).const_smul
    (ringEps R ^ 3)
  have dSum : HasFDerivAt (resFiveTerms R ν ψ pr τ) _ y :=
    (((dA1.add dB1).add dA2).add dB2).add dB3
  have hApp := congrArg (fun L : Space →L[ℝ] Space => L v) dSum.fderiv
  rw [hApp]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

/-! ### 6. Continuity in `τ` for fixed `y ∉ Axi.axis` -/

theorem continuous_chartPtR03_time (R : ℝ) (y : Space) :
    Continuous (fun τ => chartPtR03 R τ y) := by
  unfold chartPtR03 Axi.phase
  fun_prop

theorem continuous_profile_time {R : ℝ} (hR : 0 < R) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) :
    Continuous (fun τ => X (chartPtR03 R τ y)) :=
  hX.continuousOn.comp_continuous (continuous_chartPtR03_time R y)
    (fun _ => Axi.age_pos hR.ne' hy)

theorem continuous_chartVal_time {R : ℝ} (hR : 0 < R) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) :
    Continuous (fun τ => chartVal R τ X y) :=
  continuous_const.mul (continuous_profile_time hR hX hy)

theorem continuous_radLift_time {R : ℝ} (hR : 0 < R) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) :
    Continuous (fun τ => radLift R X τ y) :=
  (continuous_chartVal_time hR hX hy).smul continuous_const

theorem continuous_axLift_time {R : ℝ} (hR : 0 < R) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) :
    Continuous (fun τ => axLift R X τ y) :=
  (continuous_chartVal_time hR hX hy).smul continuous_const

theorem continuous_chartValDeriv_time {R : ℝ} (hR : 0 < R) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) (v : Space) :
    Continuous (fun τ => chartValDeriv R τ X y v) := by
  have hQ := continuous_profile_time hR (contDiffOn_partialQ hX) hy
  have hS := continuous_profile_time hR (contDiffOn_ageShift 3 hX) hy
  have hE := continuous_profile_time hR (contDiffOn_partialEta hX) hy
  unfold chartValDeriv
  exact continuous_const.mul
    ((continuous_const.mul (hQ.sub (continuous_const.mul hS))).add (continuous_const.mul hE))

theorem continuous_fderiv_radLift_time {R : ℝ} (hR : 0 < R) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) (v : Space) :
    Continuous (fun τ => fderiv ℝ (radLift R X τ) y v) := by
  have heq : (fun τ => fderiv ℝ (radLift R X τ) y v) =
      fun τ => chartValDeriv R τ X y v • Axi.eR y +
        (R⁻¹ * (Axi.age R y) ^ 2 * X (chartPtR03 R τ y)) •
          (Axi.hor v - Axi.ϱD y v • Axi.eR y) :=
    funext fun τ => (hasFDerivAt_radLift hR τ hX hy).2 v
  rw [heq]
  exact ((continuous_chartValDeriv_time hR hX hy v).smul continuous_const).add
    ((continuous_const.mul (continuous_profile_time hR hX hy)).smul continuous_const)

theorem continuous_fderiv_axLift_time {R : ℝ} (hR : 0 < R) {X : ProfilePoint → ℝ}
    (hX : ContDiffOn ℝ ∞ X ageDomain) {y : Space} (hy : y ∉ Axi.axis) (v : Space) :
    Continuous (fun τ => fderiv ℝ (axLift R X τ) y v) := by
  have heq : (fun τ => fderiv ℝ (axLift R X τ) y v) =
      fun τ => chartValDeriv R τ X y v • Axi.e3 :=
    funext fun τ => (hasFDerivAt_axLift hR τ hX hy).2 v
  rw [heq]
  exact (continuous_chartValDeriv_time hR hX hy v).smul continuous_const

theorem continuous_ringResidual_time {R ν c : ℝ} (hR : 2 ≤ R) (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr) {y : Space}
    (hy : y ∉ Axi.axis) :
    Continuous (fun τ => ringResidual R ν ψ pr τ y) := by
  have hR0 : 0 < R := by linarith
  have heq : (fun τ => ringResidual R ν ψ pr τ y) = fun τ => resFiveTerms R ν ψ pr τ y :=
    funext fun τ => ringResidual_eq_resFiveTerms hR hν hc htr τ hy
  rw [heq]
  obtain ⟨hψ, hpr⟩ := exactTrain_smooth hν hc htr
  have cA1 := (continuous_radLift_time hR0 (contDiffOn_coeffA1 ν hψ hpr) hy).const_smul (ringEps R)
  have cB1 := (continuous_radLift_time hR0 (contDiffOn_coeffB1 ν hψ) hy).const_smul (ringEps R ^ 2)
  have cA2 := (continuous_axLift_time hR0 (contDiffOn_coeffA2 ν hψ) hy).const_smul (ringEps R)
  have cB2 := (continuous_axLift_time hR0 (contDiffOn_coeffB2 ν hψ) hy).const_smul (ringEps R ^ 2)
  have cB3 := (continuous_axLift_time hR0 (contDiffOn_coeffB3 ν hψ) hy).const_smul (ringEps R ^ 3)
  exact (((cA1.add cB1).add cA2).add cB2).add cB3

theorem continuous_fderiv_ringResidual_time {R ν c : ℝ} (hR : 2 ≤ R) (hν : 0 < ν) (hc : 0 < c)
    {ψ pr : ProfilePoint → ℝ} (htr : IsExactPlanarTrain ν c ψ pr) {y : Space}
    (hy : y ∉ Axi.axis) (v : Space) :
    Continuous (fun τ => fderiv ℝ (ringResidual R ν ψ pr τ) y v) := by
  have hR0 : 0 < R := by linarith
  have heq : (fun τ => fderiv ℝ (ringResidual R ν ψ pr τ) y v) =
      fun τ =>
        ringEps R • fderiv ℝ (radLift R (coeffA₁ ν ψ pr) τ) y v +
          (ringEps R ^ 2) • fderiv ℝ (radLift R (coeffB₁ ν ψ) τ) y v +
          ringEps R • fderiv ℝ (axLift R (coeffA₂ ν ψ) τ) y v +
          (ringEps R ^ 2) • fderiv ℝ (axLift R (coeffB₂ ν ψ) τ) y v +
          (ringEps R ^ 3) • fderiv ℝ (axLift R (coeffB₃ ν ψ) τ) y v :=
    funext fun τ => fderiv_ringResidual_eq_resFiveTerms hR hν hc htr τ hy v
  rw [heq]
  obtain ⟨hψ, hpr⟩ := exactTrain_smooth hν hc htr
  have cA1 := (continuous_fderiv_radLift_time hR0 (contDiffOn_coeffA1 ν hψ hpr) hy v).const_smul
    (ringEps R)
  have cB1 := (continuous_fderiv_radLift_time hR0 (contDiffOn_coeffB1 ν hψ) hy v).const_smul
    (ringEps R ^ 2)
  have cA2 := (continuous_fderiv_axLift_time hR0 (contDiffOn_coeffA2 ν hψ) hy v).const_smul
    (ringEps R)
  have cB2 := (continuous_fderiv_axLift_time hR0 (contDiffOn_coeffB2 ν hψ) hy v).const_smul
    (ringEps R ^ 2)
  have cB3 := (continuous_fderiv_axLift_time hR0 (contDiffOn_coeffB3 ν hψ) hy v).const_smul
    (ringEps R ^ 3)
  exact (((cA1.add cB1).add cA2).add cB2).add cB3

end UnforcedLeray.Short.PartIIa.R05
