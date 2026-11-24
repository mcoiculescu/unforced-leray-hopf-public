import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs

/-!
# Phase curl equals slice curl (BSCurlSlice)

Source `the November 2 reference manuscript` lines 1351-1362.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem bsCurlSlice : BSCurlSlice := by
  intro P Θ hΘ t y
  have hdiff : DifferentiableAt ℝ Θ (t, y) :=
    (hΘ.smooth.differentiable (by simp)).differentiableAt
  have hemb : HasFDerivAt (fun y' : Space => ((t, y') : ℝ × Space))
      (ContinuousLinearMap.inr ℝ ℝ Space) y :=
    (hasFDerivAt_const t y).prodMk (hasFDerivAt_id y)
  have hcomp : HasFDerivAt (fun y' : Space => Θ (t, y'))
      ((fderiv ℝ Θ (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    hdiff.hasFDerivAt.comp y hemb
  have key : ∀ v : Space,
      fderiv ℝ (fun y' : Space => Θ (t, y')) y v = fderiv ℝ Θ (t, y) (0, v) := by
    intro v
    rw [hcomp.fderiv]
    rfl
  unfold curlT bsCurlS dy
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key]
  rfl

end UnforcedLeray.Short.PartIIIb.Concrete
