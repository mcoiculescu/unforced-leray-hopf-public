import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

/-!
# `OD_TransCont` (task `PartIII-b:C/near/pins/3/4/2/3/2/4/4`)

Strong continuity of the phase translation on `X` (`B0223.continuous_transC`, `Ops.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem odTransCont : OD_TransCont := by
  intro P _ Ψ
  exact UnforcedLeray.B0223.continuous_transC (E := UnforcedLeray.B0223.SpaceC) Ψ

end UnforcedLeray.Short.PartIIIb.NearInst
