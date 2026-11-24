import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
Helper lemmas for `inletSrcDerivBound`: slice derivatives of a jointly differentiable function
and their norm bounds.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.DerivAux

open scoped ContDiff

variable {Space V : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Spatial derivative of a time slice equals the joint derivative in the spatial direction. -/
theorem fderiv_slice_eq (F : ℝ × Space → V) (hF : Differentiable ℝ F) (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun x : Space => F (τ, x)) y v = fderiv ℝ F (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun x : Space => (τ, x))
      ((0 : Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hF (τ, y)).hasFDerivAt.comp y hmap
  have h := congrArg (fun A : Space →L[ℝ] V => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h

/-- Directional derivative of a time slice is bounded by the first iterated derivative. -/
theorem norm_fderiv_slice_le (F : Space → V) (y v : Space) :
    ‖fderiv ℝ F y v‖ ≤ ‖iteratedFDeriv ℝ 1 F y‖ * ‖v‖ := by
  rw [norm_iteratedFDeriv_one]
  exact (fderiv ℝ F y).le_opNorm v

end UnforcedLeray.Short.PartIIIb.Concrete.DerivAux

end
