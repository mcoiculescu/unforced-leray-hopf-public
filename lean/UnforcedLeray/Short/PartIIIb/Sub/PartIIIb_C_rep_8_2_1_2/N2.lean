import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `NvPd2`: the axial derivative of the ring lift (`PartIII-b:C/rep/8/2/1/2`, (N2))

Source `the November 2 reference manuscript`,
lines 5466-5476 and 2073-2077. At `y` with `y 1 = 0`, `y 0 > 0` we have `ϱ y = y 0` and
`eR y = e₀`. The derivative of `N_v` along `e₃` is `√s` times the `η`-derivative of the frame
coefficients (`axial_chain`), since `eR` and `ϱ` do not depend on `y₃` (`eRD y e₃ = 0`,
`ageD R y e₃ = 0`), and `√s · √s = s`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

theorem hor_e3_n2 : hor e3 = 0 := by
  ext j
  fin_cases j <;> simp [hor_apply_zero, hor_apply_one, hor_apply_two, e3, coordinateVector,
    EuclideanSpace.single_apply]

theorem eRD_e3_n2 (y : Space) : eRD y e3 = 0 := by
  rw [eRD_apply, ϱD_e3, hor_e3_n2]
  simp

theorem ageD_e3_n2 (R : ℝ) (y : Space) : ageD R y e3 = 0 := by
  simp [ageD, ϱD_e3]

/-- `merSp` in the basis `e₀ = e_r`, `e₂ = e_z` at azimuth zero. -/
theorem merSp_eq_n2 (D : Merid) : merSp D = D 0 • coordinateVector 0 + D 1 • e3 := by
  ext j
  fin_cases j <;> simp [merSp, vecSp, coordinateVector, e3, EuclideanSpace.single_apply]

/-- **`NvPd2`.** -/
theorem nvPd2 : NvPd2 := by
  intro R τ b y hR hy0 hy1 hb
  have hy : y ∉ axis := fun h => hy0.ne' h.1
  have hR0 : R ≠ 0 := hR.ne'
  have hage0 : age R y ≠ 0 := (age_pos hR0 hy).ne'
  have hϱ : ϱ y = y 0 := by
    unfold ϱ
    rw [hy1, show y 0 ^ 2 + (0 : ℝ) ^ 2 = y 0 ^ 2 by ring]
    exact Real.sqrt_sq hy0.le
  have hEr : eR y = coordinateVector 0 := by
    ext j
    fin_cases j <;> simp [eR_apply_zero, eR_apply_one, eR_apply_two, hϱ, hy1, hy0.ne',
      coordinateVector]
  have hbc : HasFDerivAt (fun x => b (chart R τ x))
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y)) y :=
    hb.hasFDerivAt.comp y (hasFDerivAt_chart hR0 τ hy)
  have hD : ((fderiv ℝ b (chart R τ y)).comp (chartD R y)) e3 =
      √(age R y) • UnforcedLeray.Axi.dEta b (chart R τ y) := by
    rw [← hbc.fderiv]
    exact axial_chain hR hy hb
  have hC0 : HasFDerivAt (fun x => b (chart R τ x) 0)
      ((EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).comp
        ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) y :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hbc
  have hC1 : HasFDerivAt (fun x => b (chart R τ x) 1)
      ((EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).comp
        ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) y :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hbc
  have hS := (hasFDerivAt_age R hy).sqrt hage0
  have hL0 := hS.mul hC0
  have hL1 := hS.mul hC1
  have hNv : Nv R b τ = fun z => (√(age R z) * b (chart R τ z) 0) • eR z +
      (√(age R z) * b (chart R τ z) 1) • e3 := by
    funext z
    simp only [Nv, frameL_apply, smul_add, smul_smul]
  have hTot := (hL0.smul (hasFDerivAt_eR hy)).add (hL1.smul_const e3)
  have hP0 : ((EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).comp
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) e3 = √(age R y) * UnforcedLeray.Axi.dEta b (chart R τ y) 0 := by
    rw [ContinuousLinearMap.comp_apply, hD]
    simp
  have hP1 : ((EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).comp
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) e3 = √(age R y) * UnforcedLeray.Axi.dEta b (chart R τ y) 1 := by
    rw [ContinuousLinearMap.comp_apply, hD]
    simp
  unfold physPd
  change fderiv ℝ (Nv R b τ) y e3 = _
  rw [hNv]
  have key : fderiv ℝ (fun z => (√(age R z) * b (chart R τ z) 0) • eR z +
      (√(age R z) * b (chart R τ z) 1) • e3) y = _ := hTot.fderiv
  rw [key]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, eRD_e3_n2, ageD_e3_n2, smul_zero, zero_add,
    ContinuousLinearMap.smul_apply, smul_eq_mul, hP0, hP1]
  rw [hEr, merSp_eq_n2]
  have hsq : √(age R y) * √(age R y) = age R y := Real.mul_self_sqrt (age_nonneg R y)
  conv_rhs => rw [← hsq]
  module

end UnforcedLeray.Short.PartIIIb.Concrete
