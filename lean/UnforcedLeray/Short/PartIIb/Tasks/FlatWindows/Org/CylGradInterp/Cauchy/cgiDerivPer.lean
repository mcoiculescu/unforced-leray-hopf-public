import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6_1

/-!
# `CgiDerivPer`: derivatives of a nice function are `q`-periodic everywhere (SP 1932-1933)

`qShift c` is the translation by `v = (0, (c, 0))`, so `w = w ∘ (· + v)` and `fderiv` commutes
with the translation.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem qShift_eq_add_v (c : ℝ) (x : Coord) : qShift c x = x + (0, (c, 0)) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [qShift]

theorem cgiDerivPer_proof : UnforcedLeray.Short.IIb.CgiDerivPer := by
  intro r c w hw i x
  have hfun : (fun y : Coord => w (y + (0, (c, 0)))) = w :=
    funext fun y => by rw [← qShift_eq_add_v]; exact hw.periodic y
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := w) (x := x) (0, (c, 0))
  rw [hfun] at hd
  unfold cdv
  rw [qShift_eq_add_v, ← hd]

end UnforcedLeray.Short.IIb
