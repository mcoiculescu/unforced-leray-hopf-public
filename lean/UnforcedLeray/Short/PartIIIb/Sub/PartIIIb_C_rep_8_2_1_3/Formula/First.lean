import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula.Smooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N0
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N1

/-!
# First derivatives of the framed profile (`PartIII-b:C/rep/8/2/1/3/a`, helper 2)

Source lines 5036-5045.  For `G y' = frameL y' (B (chart R τ y'))`:
`DG(y') v = frameL y' (DB (χ y') (Dχ y' v)) + B₀(χ y') De_r(y') v`, and the three
first derivatives at azimuth zero, and the general-azimuth hoop derivative.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux

open UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete

/-- The framed profile. -/
def Gf (R τ : ℝ) (B : ℝ × (ℝ × ℝ) → Merid) : Space → Space :=
  fun y' => frameL y' (B (chart R τ y'))

theorem hasFDerivAt_Gf {R τ : ℝ} {B : ℝ × (ℝ × ℝ) → Merid} (hR : 0 < R) {y : Space}
    (hy : y ∉ axis) (hB : DifferentiableAt ℝ B (chart R τ y)) :
    HasFDerivAt (Gf R τ B)
      (((B (chart R τ y) 0) • eRD y +
        ((EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).comp
          ((fderiv ℝ B (chart R τ y)).comp (chartD R y))).smulRight (eR y)) +
        ((EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).comp
          ((fderiv ℝ B (chart R τ y)).comp (chartD R y))).smulRight e3) y := by
  have hR0 : R ≠ 0 := hR.ne'
  have hbc : HasFDerivAt (fun x => B (chart R τ x))
      ((fderiv ℝ B (chart R τ y)).comp (chartD R y)) y :=
    hB.hasFDerivAt.comp y (hasFDerivAt_chart hR0 τ hy)
  have hC0 := (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hbc
  have hC1 := (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hbc
  have hG : Gf R τ B = fun z => (B (chart R τ z) 0) • eR z + (B (chart R τ z) 1) • e3 := by
    funext z
    simp only [Gf, frameL_apply]
  rw [hG]
  exact (hC0.smul (hasFDerivAt_eR hy)).add (hC1.smul_const e3)

theorem fderiv_Gf_apply {R τ : ℝ} {B : ℝ × (ℝ × ℝ) → Merid} (hR : 0 < R) {y : Space}
    (hy : y ∉ axis) (hB : DifferentiableAt ℝ B (chart R τ y)) (v : Space) :
    fderiv ℝ (Gf R τ B) y v =
      frameL y (fderiv ℝ B (chart R τ y) (chartD R y v)) + (B (chart R τ y) 0) • eRD y v := by
  rw [(hasFDerivAt_Gf hR hy hB).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, frameL_apply,
    EuclideanSpace.coe_proj]
  abel

theorem ϱ_az {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) : ϱ y = y 0 := by
  unfold ϱ
  rw [hy1, show y 0 ^ 2 + (0 : ℝ) ^ 2 = y 0 ^ 2 by ring]
  exact Real.sqrt_sq hy0.le

theorem eR_az {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) : eR y = coordinateVector 0 := by
  ext j
  fin_cases j <;> simp [eR_apply_zero, eR_apply_one, eR_apply_two, ϱ_az hy0 hy1, hy1, hy0.ne',
    coordinateVector]

theorem not_axis_az {y : Space} (hy0 : 0 < y 0) : y ∉ axis := fun h => hy0.ne' h.1

theorem eRD_e3_zero (y : Space) : eRD y e3 = 0 := by
  rw [eRD_apply, ϱD_e3]
  have : hor e3 = 0 := by
    ext j
    fin_cases j <;> simp [hor_apply_zero, hor_apply_one, hor_apply_two, e3, coordinateVector,
      coordinateVector_apply]
  rw [this]
  simp

/-- `∂_0 G = merSp (Dρ B ∘ χ)` at azimuth zero. -/
theorem physPd_Gf_zero {R τ : ℝ} {B : ℝ × (ℝ × ℝ) → Merid} (hR : 0 < R) {y : Space}
    (hy0 : 0 < y 0) (hy1 : y 1 = 0) (hB : DifferentiableAt ℝ B (chart R τ y)) :
    physPd (Gf R τ B) 0 y = merSp (Drho R⁻¹ B (chart R τ y)) := by
  have hy := not_axis_az hy0
  have hE := eR_az hy0 hy1
  unfold physPd
  rw [← hE, fderiv_Gf_apply hR hy hB, ← fderiv_comp_chart_apply hR.ne' hy hB,
    radial_chain hR hy hB, eRD_eR_zero_local hy, smul_zero, add_zero, frameL_apply, hE,
    merSp_eq_local]
  rfl

/-- `∂_2 G = merSp (Dz B ∘ χ)` at azimuth zero. -/
theorem physPd_Gf_two {R τ : ℝ} {B : ℝ × (ℝ × ℝ) → Merid} (hR : 0 < R) {y : Space}
    (hy0 : 0 < y 0) (hy1 : y 1 = 0) (hB : DifferentiableAt ℝ B (chart R τ y)) :
    physPd (Gf R τ B) 2 y = merSp (Dz B (chart R τ y)) := by
  have hy := not_axis_az hy0
  have hE := eR_az hy0 hy1
  have h2 : (coordinateVector 2 : Space) = e3 := rfl
  unfold physPd
  rw [h2, fderiv_Gf_apply hR hy hB, ← fderiv_comp_chart_apply hR.ne' hy hB,
    axial_chain hR hy hB, eRD_e3_zero, smul_zero, add_zero, frameL_apply, hE,
    merSp_eq_local]
  rfl

/-- `∂_1 G = (B₀ ∘ χ / y₀) e₁` at azimuth zero. -/
theorem physPd_Gf_one {R τ : ℝ} {B : ℝ × (ℝ × ℝ) → Merid} (hR : 0 < R) {y : Space}
    (hy0 : 0 < y 0) (hy1 : y 1 = 0) (hB : DifferentiableAt ℝ B (chart R τ y)) :
    physPd (Gf R τ B) 1 y = (B (chart R τ y) 0 / y 0) • coordinateVector 1 := by
  have hy := not_axis_az hy0
  have hch1 : chartD R y (coordinateVector 1) = 0 := by
    rw [chartD_apply, ϱD_e1_n1 hy1]
    simp [coordinateVector_apply]
  unfold physPd
  rw [fderiv_Gf_apply hR hy hB, hch1, map_zero, eRD_e1_n1 hy0 hy1, map_zero, smul_smul]
  simp [div_eq_mul_inv]

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2FormulaAux
