import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDecomp
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterDict
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen

/-!
# `GenAdjointPair` (task `PartIII-b:C/near/pins/3/4/2`)

Unconditional form of `genAdjointPair_of` (Sub/PartIII-b_C_near_pins_3_4_2.lean), applied to the
three leaves `chartDecomp` (ChartDecomp.lean), `outerDict` (OuterDict.lean) and `outerGen`
(OuterGen.lean).  Source `shorter-proof-2026-11-02.tex` lines 1339-1362, 3346-3352, 4139-4146.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem genAdjointPair : GenAdjointPair :=
  genAdjointPair_of chartDecomp outerDict outerGen

end UnforcedLeray.Short.PartIIIb.NearInst
