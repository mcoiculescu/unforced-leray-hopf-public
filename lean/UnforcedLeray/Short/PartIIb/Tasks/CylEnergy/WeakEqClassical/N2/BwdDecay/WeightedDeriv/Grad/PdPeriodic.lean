import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2_1

/-!

`c`-periodic.

Source: `the November 2 reference manuscript` lines 2100-2105.

Translation by `(c, 0)` leaves `f` invariant, so the derivative at `x + (c,0)` equals the derivative
at `x` (`fderiv_comp_add_right`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem pdPeriodic : UnforcedLeray.Short.IIb.PdPeriodic := by
  intro c f j hf x
  have hfun : (fun y : B0579.Plane => f (y + ((c, 0) : B0579.Plane))) = f := by
    funext y
    have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hf y
  have key : fderiv ℝ f (x + ((c, 0) : B0579.Plane)) = fderiv ℝ f x := by
    have h : fderiv ℝ (fun t : B0579.Plane => f (t + ((c, 0) : B0579.Plane))) x =
        fderiv ℝ f (x + ((c, 0) : B0579.Plane)) := fderiv_comp_add_right _
    rw [hfun] at h
    exact h.symm
  have hx : x + ((c, 0) : B0579.Plane) = (x.1 + c, x.2) := by ext <;> simp
  unfold B0579.pd
  rw [← hx, key]

end UnforcedLeray.Short.IIb
