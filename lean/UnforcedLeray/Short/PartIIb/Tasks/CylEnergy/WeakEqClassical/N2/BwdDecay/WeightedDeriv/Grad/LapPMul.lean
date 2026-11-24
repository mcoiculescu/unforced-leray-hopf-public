import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- Product rule for a first partial derivative at a point. -/
theorem lapPMul_pd_mul (j : Fin 2) (u v : B0579.Plane → ℝ) (x : B0579.Plane)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    B0579.pd j (fun y => u y * v y) x = u x * B0579.pd j v x + v x * B0579.pd j u x := by
  unfold B0579.pd
  have h : HasFDerivAt (fun y => u y * v y) (u x • fderiv ℝ v x + v x • fderiv ℝ u x) x :=
    hu.hasFDerivAt.mul hv.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Additivity of a first partial derivative at a point. -/
theorem lapPMul_pd_add (j : Fin 2) (u v : B0579.Plane → ℝ) (x : B0579.Plane)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    B0579.pd j (fun y => u y + v y) x = B0579.pd j u x + B0579.pd j v x := by
  unfold B0579.pd
  have h : HasFDerivAt (fun y => u y + v y) (fderiv ℝ u x + fderiv ℝ v x) x :=
    hu.hasFDerivAt.add hv.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.add_apply]

/-- A first partial of a `C^2` function is differentiable. -/
theorem lapPMul_pd_diff (j : Fin 2) (h : B0579.Plane → ℝ) (hh : ContDiff ℝ 2 h) :
    Differentiable ℝ (B0579.pd j h) := by
  intro y
  have h1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ h) y := (h1.differentiable (by norm_num)) y
  exact h2.clm_apply (differentiableAt_const _)

/-- Diagonal second partial of a product of `C^2` functions. -/
theorem lapPMul_pd_pd (i : Fin 2) (f g : B0579.Plane → ℝ) (x : B0579.Plane)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    B0579.pd i (B0579.pd i (fun y => f y * g y)) x =
      f x * B0579.pd i (B0579.pd i g) x + g x * B0579.pd i (B0579.pd i f) x +
        2 * (B0579.pd i f x * B0579.pd i g x) := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdg : Differentiable ℝ g := hg.differentiable (by norm_num)
  have e1 : B0579.pd i (fun y => f y * g y) =
      fun y => f y * B0579.pd i g y + g y * B0579.pd i f y := by
    funext y
    exact lapPMul_pd_mul i f g y (hdf y) (hdg y)
  rw [e1]
  rw [lapPMul_pd_add i (fun y => f y * B0579.pd i g y) (fun y => g y * B0579.pd i f y) x
    ((hdf x).mul (lapPMul_pd_diff i g hg x)) ((hdg x).mul (lapPMul_pd_diff i f hf x))]
  rw [lapPMul_pd_mul i f (B0579.pd i g) x (hdf x) (lapPMul_pd_diff i g hg x)]
  rw [lapPMul_pd_mul i g (B0579.pd i f) x (hdg x) (lapPMul_pd_diff i f hf x)]
  ring

theorem lapPMul : UnforcedLeray.Short.IIb.LapPMul := by
  intro f g x hf hg
  unfold lapP
  rw [lapPMul_pd_pd 0 f g x hf hg, lapPMul_pd_pd 1 f g x hf hg]
  ring

end UnforcedLeray.Short.IIb
