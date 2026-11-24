import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_5_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.VelPairAE
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Smooth.DivReal
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressMapWeakSol.Smooth.DivPer

/-!
# `PartIII-b:C/near/pins/5/2`: `SWSmooth`

Source `the November 2 reference manuscript`
3888-3890, 1675-1679, 1660-1665, 1556-1572.

`swSmooth_of` (Sub 5/2) reduces `SWSmooth` to `VelPairAE`, `SWDivEpsReal` and `SWDivEpsPer`, which
are proved in `Proofs/VelPairAE.lean`, `Smooth/DivReal.lean` and `Smooth/DivPer.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- **`SWSmooth`** (source 3888-3890, 1675-1679): the smooth-stress weak-solution property. -/
theorem swSmooth : SWSmooth := swSmooth_of velPairAE swDivEpsReal swDivEpsPer

end UnforcedLeray.Short.PartIIIb.NearInst
