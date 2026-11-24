import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_9_5_1
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut.Leaves.ParamInt7.Diff

/-!
# Proof of `SCParamInt7` (source 4178-4186, 4917-4937)

Finite-order differentiation under the integral over `Ioi 1` on the domain `Vec3`; the
induction on the order is carried out in `ParamInt7/Diff.lean` (`ParamInt7Aux.paramDiff`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem scParamInt7 : SCParamInt7 := by
  unfold SCParamInt7
  intro U F hU hF hM hD
  exact ParamInt7Aux.paramDiff 7 U F hU hF hM hD

end UnforcedLeray.Short.PartIIIb.Concrete
