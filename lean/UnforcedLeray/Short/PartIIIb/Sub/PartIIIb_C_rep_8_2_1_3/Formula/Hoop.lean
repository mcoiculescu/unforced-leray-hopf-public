import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula.Entries

/-!
# The hoop-hoop entry (`PartIII-b:C/rep/8/2/1/3/a`, helper 5)

General-azimuth formula for `∂_1 G` and its derivative along the circle through `y`
(on which the chart is constant).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete

theorem physPd_Gf_one_gen {R τ : ℝ} {B : ℝ × (ℝ × ℝ) → Merid} (hR : 0 < R) {y : Space}
    (hy : y ∉ axis) (hB : DifferentiableAt ℝ B (chart R τ y)) :
    physPd (Gf R τ B) 1 y =
      (ϱD y (coordinateVector 1)) • frameL y (Drho R⁻¹ B (chart R τ y)) +
        (B (chart R τ y) 0) • ((ϱ y)⁻¹ • (coordinateVector 1 - ϱD y (coordinateVector 1) • eR y)) := by
  have hc : chartD R y (coordinateVector 1) =
      (ϱD y (coordinateVector 1)) • chartD R y (eR y) := by
    rw [chartD_apply, chartD_apply, ϱD_eR hy]
    simp only [eR_apply_two, coordinateVector_apply, Prod.smul_mk, smul_eq_mul]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (try simp) <;> (try ring)
  have hD : fderiv ℝ B (chart R τ y) (chartD R y (eR y)) = Drho R⁻¹ B (chart R τ y) := by
    rw [← fderiv_comp_chart_apply hR.ne' hy hB, radial_chain hR hy hB]
    rfl
  unfold physPd
  rw [fderiv_Gf_apply hR hy hB, hc, map_smul, hD, map_smul, eRD_apply, hor_e1_n1]

/-- On the circle through `y`, the chart is constant and the circle is parametrised by
`γ t = ρ cos t e₀ + ρ sin t e₁ + z e₃`. -/
def circ (ρ z t : ℝ) : Space :=
  (ρ * Real.cos t) • (coordinateVector 0 : Space) + (ρ * Real.sin t) • (coordinateVector 1 : Space) +
    z • e3

theorem circ_apply0 (ρ z t : ℝ) : circ ρ z t 0 = ρ * Real.cos t := by
  simp [circ, coordinateVector_apply]
theorem circ_apply1 (ρ z t : ℝ) : circ ρ z t 1 = ρ * Real.sin t := by
  simp [circ, coordinateVector_apply]
theorem circ_apply2 (ρ z t : ℝ) : circ ρ z t 2 = z := by
  simp [circ, coordinateVector_apply]

theorem ϱ_circ {ρ : ℝ} (hρ : 0 < ρ) (z t : ℝ) : ϱ (circ ρ z t) = ρ := by
  unfold ϱ
  rw [circ_apply0, circ_apply1]
  have : (ρ * Real.cos t) ^ 2 + (ρ * Real.sin t) ^ 2 = ρ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [this]
  exact Real.sqrt_sq hρ.le

theorem circ_not_axis {ρ : ℝ} (hρ : 0 < ρ) (z t : ℝ) : circ ρ z t ∉ axis := by
  intro h
  have := (mem_axis_iff _).1 h
  rw [ϱ_circ hρ] at this
  exact hρ.ne' this

theorem chart_circ {R τ ρ : ℝ} (hρ : 0 < ρ) (z t : ℝ) :
    chart R τ (circ ρ z t) = chart R τ (circ ρ z 0) := by
  simp only [chart, age, phase, UnforcedLeray.Axi.trans, ϱ_circ hρ, circ_apply2 ρ z]

theorem circ_zero {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    circ (y 0) (y 2) 0 = y := by
  ext j
  fin_cases j <;> simp [circ_apply0, circ_apply1, circ_apply2, hy1]

theorem hasDerivAt_circ (ρ z : ℝ) :
    HasDerivAt (circ ρ z) (ρ • (coordinateVector 1 : Space)) 0 := by
  have h0 := ((Real.hasDerivAt_cos (0:ℝ)).const_mul ρ).smul_const (coordinateVector 0 : Space)
  have h1 := ((Real.hasDerivAt_sin (0:ℝ)).const_mul ρ).smul_const (coordinateVector 1 : Space)
  have := (h0.add h1).add_const (z • e3)
  refine this.congr_deriv ?_
  simp


theorem eR_circ {ρ : ℝ} (hρ : 0 < ρ) (z t : ℝ) :
    eR (circ ρ z t) = Real.cos t • (coordinateVector 0 : Space) +
      Real.sin t • (coordinateVector 1 : Space) := by
  ext j
  fin_cases j <;> simp [eR_apply_zero, eR_apply_one, eR_apply_two, circ_apply0, circ_apply1,
    ϱ_circ hρ, hρ.ne', coordinateVector_apply]

theorem ϱD_circ {ρ : ℝ} (hρ : 0 < ρ) (z t : ℝ) :
    ϱD (circ ρ z t) (coordinateVector 1) = Real.sin t := by
  rw [ϱD_apply, ϱ_circ hρ, circ_apply0, circ_apply1]
  simp [coordinateVector_apply]
  field_simp

theorem entry_11_raw {R τ : ℝ} (hR : 0 < R) {B : ℝ × (ℝ × ℝ) → Merid}
    (hB : ContDiffOn ℝ 2 B SProf) {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    (y 0) • physPd2 (Gf R τ B) 1 1 y =
      (Drho R⁻¹ B (chart R τ y) 0 - B (chart R τ y) 0 * (y 0)⁻¹) • (coordinateVector 0 : Space) +
        (Drho R⁻¹ B (chart R τ y) 1) • e3 := by
  have hy := not_axis_az hy0
  have hρ := hy0
  set ρ := y 0 with hρdef
  have hGa : ContDiffAt ℝ 2 (Gf R τ B) y := contDiffAt_frame R τ hR B hB hy
  have hBa := contDiffAt_prof (τ := τ) hR hB hy
  have hd : DifferentiableAt ℝ (fderiv ℝ (Gf R τ B)) y :=
    (hGa.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hΦ' : DifferentiableAt ℝ (fun y' => physPd (Gf R τ B) 1 y') y :=
    (ContinuousLinearMap.apply ℝ Space (coordinateVector 1)).differentiableAt.comp y hd
  have hc0 := circ_zero hy0 hy1
  have hΦ'' : HasFDerivAt (fun y' => physPd (Gf R τ B) 1 y')
      (fderiv ℝ (fun y' => physPd (Gf R τ B) 1 y') y) (circ ρ (y 2) 0) := by
    rw [hc0]; exact hΦ'.hasFDerivAt
  have h1 := hΦ''.comp_hasDerivAt (0:ℝ) (hasDerivAt_circ ρ (y 2))
  rw [map_smul] at h1
  have e11 : fderiv ℝ (fun y' => physPd (Gf R τ B) 1 y') y (coordinateVector 1) =
      physPd2 (Gf R τ B) 1 1 y := rfl
  rw [e11] at h1
  -- the explicit curve
  set D := Drho R⁻¹ B (chart R τ y) with hD
  set b0 := B (chart R τ y) 0 with hb0
  have hφ : ∀ t : ℝ, physPd (Gf R τ B) 1 (circ ρ (y 2) t) =
      Real.sin t • (D 0 • (Real.cos t • (coordinateVector 0 : Space) +
          Real.sin t • (coordinateVector 1 : Space)) + D 1 • e3) +
        b0 • (ρ⁻¹ • (coordinateVector 1 - Real.sin t • (Real.cos t • (coordinateVector 0 : Space) +
          Real.sin t • (coordinateVector 1 : Space)))) := by
    intro t
    have hch : chart R τ (circ ρ (y 2) t) = chart R τ y := by
      rw [chart_circ hρ, hc0]
    have hBt : DifferentiableAt ℝ B (chart R τ (circ ρ (y 2) t)) := by
      rw [hch]; exact hBa.differentiableAt (by norm_num)
    rw [physPd_Gf_one_gen hR (circ_not_axis hρ _ t) hBt, hch, ϱD_circ hρ, ϱ_circ hρ,
      eR_circ hρ, frameL_apply, eR_circ hρ]
  have hfun : (fun y' => physPd (Gf R τ B) 1 y') ∘ circ ρ (y 2) = fun t =>
      Real.sin t • (D 0 • (Real.cos t • (coordinateVector 0 : Space) +
          Real.sin t • (coordinateVector 1 : Space)) + D 1 • e3) +
        b0 • (ρ⁻¹ • (coordinateVector 1 - Real.sin t • (Real.cos t • (coordinateVector 0 : Space) +
          Real.sin t • (coordinateVector 1 : Space)))) := funext hφ
  rw [hfun] at h1
  have hE : HasDerivAt (fun t : ℝ => Real.cos t • (coordinateVector 0 : Space) +
      Real.sin t • (coordinateVector 1 : Space)) (coordinateVector 1 : Space) 0 := by
    have := ((Real.hasDerivAt_cos (0:ℝ)).smul_const (coordinateVector 0 : Space)).add
      ((Real.hasDerivAt_sin (0:ℝ)).smul_const (coordinateVector 1 : Space))
    refine this.congr_deriv ?_
    simp
  have hP := ((hE.const_smul (D 0)).add_const (D 1 • e3))
  have hψ1 := (Real.hasDerivAt_sin (0:ℝ)).smul hP
  have hψ2 := (hE.const_smul (1:ℝ)).const_sub (coordinateVector 1 : Space)
  have hψ3 := ((Real.hasDerivAt_sin (0:ℝ)).smul hE)
  have hψ4 := (hψ3.const_sub (coordinateVector 1 : Space)).const_smul ρ⁻¹
  have hψ5 := hψ4.const_smul b0
  have hψ := hψ1.add hψ5
  have := h1.unique hψ
  rw [this]
  simp only [Real.sin_zero, Real.cos_zero, zero_smul, one_smul, add_zero, zero_add, sub_zero,
    smul_zero, smul_add, smul_sub, smul_smul]
  ext j
  fin_cases j <;> simp [coordinateVector_apply] <;> field_simp <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux
