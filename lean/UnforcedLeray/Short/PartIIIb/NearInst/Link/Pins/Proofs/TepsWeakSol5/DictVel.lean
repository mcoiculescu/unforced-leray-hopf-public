import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_5_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.DictVel.DictQmp
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.DictVel.DictAe
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.DictVel.DictChart
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.DictVel.DictFrame
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol5.DictVel.DictScalar

/-!
# `dictVel` (task `PartIII-b:C/near/pins/3/5/1`)

Assembles the five leaves `dictQmp`, `dictAe`, `dictChart`, `dictFrame`, `dictScalar`
through `dictVel_of` (Sub file `PartIII-b_C_near_pins_3_5_1`, source lines 2666-2668,
2683, 1640-1641, 1675-1677).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem dictVel : DictVel :=
  dictVel_of dictQmp dictAe dictChart dictFrame dictScalar

end UnforcedLeray.Short.PartIIIb.NearInst
