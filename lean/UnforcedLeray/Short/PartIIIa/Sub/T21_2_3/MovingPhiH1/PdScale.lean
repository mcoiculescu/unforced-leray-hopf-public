import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_3

/-!
# Part III-a, task `PartIII-a:T21/2/3/3/3`: chain rule for the moving adjoint (SP 3044, 3074-3075)

`movingPhi ν φ t y = a⁻¹ φ(√a y)` with `a = clockA ν t`, so
`∂_j (movingPhi) y = a⁻¹ √a (∂_j φ)(√a y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem mpPdScale : MpPdScale := by
  intro ν hν t ht φ hφ j y
  have ha : 0 < clockA ν t := by unfold clockA; positivity
  have hdiff : Differentiable ℝ (φ t) := hφ.differentiable (by simp)
  have hsm : HasFDerivAt (fun z : ℝ × ℝ => Real.sqrt (clockA ν t) • z)
      (Real.sqrt (clockA ν t) • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (Real.sqrt (clockA ν t) • ContinuousLinearMap.id ℝ (ℝ × ℝ)).hasFDerivAt (x := y)
  have hcomp : HasFDerivAt (fun z : ℝ × ℝ => φ t (Real.sqrt (clockA ν t) • z))
      ((fderiv ℝ (φ t) (Real.sqrt (clockA ν t) • y)).comp
        (Real.sqrt (clockA ν t) • ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hdiff _).hasFDerivAt.comp y hsm
  have hmul := hcomp.const_mul ((((clockA ν t)⁻¹ : ℝ)) : ℂ)
  have hsy : ∀ z : ℝ × ℝ, Real.sqrt (clockA ν t) • z =
      (Real.sqrt (clockA ν t) * z.1, Real.sqrt (clockA ν t) * z.2) := fun z => rfl
  have e : movingPhi ν φ t = fun z : ℝ × ℝ =>
      (((clockA ν t)⁻¹ : ℝ) : ℂ) * φ t (Real.sqrt (clockA ν t) • z) := by
    funext z
    rw [hsy z]
    rfl
  unfold pdCx
  rw [e, hmul.fderiv, hsy y]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, B0579.dir, Complex.real_smul]
  push_cast
  ring

end UnforcedLeray.Short.IIIa
