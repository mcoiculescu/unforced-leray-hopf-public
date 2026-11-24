import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2

/-!
# `NvPd1`: the hoop derivative of the ring lift (`PartIII-b:C/rep/8/2/1/2`, (N1))

Source `the November 2 reference manuscript`,
lines 5466-5476 and 2073-2077. At `y` with `y 1 = 0`, `y 0 > 0`, the direction `e₂ = coordinateVector 1`
is tangential: `ϱD y e₂ = y 1 / ϱ = 0`, so `chartD R y e₂ = 0` and the scalar factors
`√age · b_k ∘ chart` have zero derivative along `e₂`. Only `eR` moves, with
`eRD y e₂ = ϱ⁻¹ e₂`, so `∂_{y₂} N_v = √s · b₀ · ϱ⁻¹ e₂ = R⁻¹ s b₀ e₂` since `√s = R/ϱ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Axi

theorem hor_e1_n1 : hor (coordinateVector 1 : Space) = coordinateVector 1 := by
  ext j
  fin_cases j <;> simp [hor_apply_zero, hor_apply_one, hor_apply_two, coordinateVector,
    coordinateVector_apply]

theorem ϱD_e1_n1 {y : Space} (hy1 : y 1 = 0) : ϱD y (coordinateVector 1) = 0 := by
  rw [ϱD_apply]
  simp [hy1, coordinateVector_apply]

theorem ageD_e1_n1 (R : ℝ) {y : Space} (hy1 : y 1 = 0) : ageD R y (coordinateVector 1) = 0 := by
  simp [ageD, ϱD_e1_n1 hy1]

theorem eRD_e1_n1 {y : Space} (hy0 : 0 < y 0) (hy1 : y 1 = 0) :
    eRD y (coordinateVector 1) = (y 0)⁻¹ • coordinateVector 1 := by
  have hϱ : ϱ y = y 0 := by
    unfold ϱ
    rw [hy1, show y 0 ^ 2 + (0 : ℝ) ^ 2 = y 0 ^ 2 by ring]
    exact Real.sqrt_sq hy0.le
  rw [eRD_apply, ϱD_e1_n1 hy1, hor_e1_n1, zero_smul, sub_zero, hϱ]

theorem merSp_eq_n1 (D : Merid) : merSp D = D 0 • coordinateVector 0 + D 1 • e3 := by
  ext j
  fin_cases j <;> simp [merSp, vecSp, coordinateVector, e3]

/-- **`NvPd1`.** -/
theorem nvPd1 : NvPd1 := by
  intro R τ b y hR hy0 hy1 hb
  have hy : y ∉ axis := fun h => hy0.ne' h.1
  have hR0 : R ≠ 0 := hR.ne'
  have hage0 : age R y ≠ 0 := (age_pos hR0 hy).ne'
  have hϱ : ϱ y = y 0 := by
    unfold ϱ
    rw [hy1, show y 0 ^ 2 + (0 : ℝ) ^ 2 = y 0 ^ 2 by ring]
    exact Real.sqrt_sq hy0.le
  have hbc : HasFDerivAt (fun x => b (chart R τ x))
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y)) y :=
    hb.hasFDerivAt.comp y (hasFDerivAt_chart hR0 τ hy)
  have hch1 : chartD R y (coordinateVector 1) = 0 := by
    rw [chartD_apply, ϱD_e1_n1 hy1]
    simp [coordinateVector_apply]
  have hD1 : ((fderiv ℝ b (chart R τ y)).comp (chartD R y)) (coordinateVector 1) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hch1, map_zero]
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
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) (coordinateVector 1) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hD1, map_zero]
  have hP1 : ((EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).comp
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) (coordinateVector 1) = 0 := by
    rw [ContinuousLinearMap.comp_apply, hD1, map_zero]
  unfold physPd
  change fderiv ℝ (Nv R b τ) y (coordinateVector 1) = _
  rw [hNv]
  have key : fderiv ℝ (fun z => (√(age R z) * b (chart R τ z) 0) • eR z +
      (√(age R z) * b (chart R τ z) 1) • e3) y = _ := hTot.fderiv
  rw [key]
  have hE := eRD_e1_n1 hy0 hy1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ageD_e1_n1 R hy1, hP0, hP1, hE, smul_zero, zero_add,
    add_zero, smul_eq_mul, mul_zero, ContinuousLinearMap.comp_apply, map_zero, Pi.mul_apply,
    zero_smul]
  have hy0ne : y 0 ≠ 0 := hy0.ne'
  rw [sqrt_age hR hy]
  simp only [age, hϱ]
  ext j
  fin_cases j <;> simp [vecSp, coordinateVector, PiLp.smul_apply] <;> field_simp <;> ring

end UnforcedLeray.Short.PartIIIb.Concrete
