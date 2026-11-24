import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ringT0Rule : RingT0Rule := by
  intro R hR b τ y hy hF
  have hR0 : R ≠ 0 := hR.ne'
  have hρ : ϱ y ≠ 0 := ϱ_ne_zero hy
  have hage : 0 < age R y := age_pos hR0 hy
  have harg : chartD R y y = (-2 * age R y, (R, (0 : ℝ))) := by
    simp only [chartD_apply, ϱD_self hy, age]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · field_simp
    · field_simp
    · field_simp
      ring
  have hWy : (fderiv ℝ b (chart R τ y)) (chartD R y y)
      = (-2 * age R y) • UnforcedLeray.Axi.dS b (chart R τ y)
        + R • UnforcedLeray.Axi.dQ b (chart R τ y) := by
    rw [harg, clm_triple]
    simp [UnforcedLeray.Axi.dS, UnforcedLeray.Axi.dQ]
  have hH : HasFDerivAt (fun x => b (chart R τ x))
      ((fderiv ℝ b (chart R τ y)).comp (chartD R y)) y :=
    hF.hasFDerivAt.comp y (hasFDerivAt_chart hR0 τ hy)
  have hH0 : HasFDerivAt (fun x => b (chart R τ x) 0)
      ((EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).comp
        ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) y :=
    (EuclideanSpace.proj (0 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hH
  have hH1 : HasFDerivAt (fun x => b (chart R τ x) 1)
      ((EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).comp
        ((fderiv ℝ b (chart R τ y)).comp (chartD R y))) y :=
    (EuclideanSpace.proj (1 : Fin 2) : Merid →L[ℝ] ℝ).hasFDerivAt.comp y hH
  have hs : HasFDerivAt (fun x => √(age R x))
      ((1 / (2 * √(age R y))) • ageD R y) y :=
    (hasFDerivAt_age R hy).sqrt (by positivity)
  have heR : HasFDerivAt eR (eRD y) y := hasFDerivAt_eR hy
  have hA := hH0.smul heR
  have hB := hH1.smul_const e3
  have hC := hA.add hB
  have hD := hs.smul hC
  have hD2 : HasFDerivAt (fun x => √(age R x) •
      (b (chart R τ x) 0 • eR x + b (chart R τ x) 1 • e3)) _ y := hD
  have hfun : Nv R b τ = fun x => √(age R x) •
      (b (chart R τ x) 0 • eR x + b (chart R τ x) 1 • e3) := by
    funext x
    simp [Nv, frameL_apply]
  have hEy : eRD y y = 0 := by
    rw [eRD_apply, ϱD_self hy, hor_eq_smul_eR hy, sub_self, smul_zero]
  have hDs : (1 / (2 * √(age R y))) * (ageD R y y) = -√(age R y) := by
    rw [ageD, ContinuousLinearMap.smul_apply, ϱD_self hy, sqrt_age hR hy, smul_eq_mul]
    field_simp
  have hval : fderiv ℝ (Nv R b τ) y y
      = √(age R y) • frameL y (fderiv ℝ b (chart R τ y) (chartD R y y))
        + (-√(age R y)) • frameL y (b (chart R τ y)) := by
    rw [hfun, hD2.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      EuclideanSpace.coe_proj, hEy, smul_zero, zero_add, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, frameL_apply, hDs]
    rfl
  have hτ : HasDerivAt (fun t => Nv R b t y)
      (√(age R y) • frameL y ((R / 2 : ℝ) • UnforcedLeray.Axi.dQ b (chart R τ y))) τ := by
    have h1 := (frameL y).hasFDerivAt.comp_hasDerivAt τ (phase_chain y hF)
    exact h1.const_smul (√(age R y))
  show deriv (fun t => Nv R b t y) τ - (1 / 2 : ℝ) • fderiv ℝ (Nv R b τ) y y
      - (1 / 2 : ℝ) • Nv R b τ y
    = Nv R (fun p => p.1 • UnforcedLeray.Axi.dS b p) τ y
  rw [hτ.deriv, hval, hWy]
  have hc1 : (chart R τ y).1 = age R y := rfl
  simp only [Nv, map_add, map_smul, hc1]
  module
