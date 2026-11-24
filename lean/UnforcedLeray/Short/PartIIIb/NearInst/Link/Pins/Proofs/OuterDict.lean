import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterDict.Scaled
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterDict.PairIter
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterDict.VelSlice

/-!
# `OuterDict` (task `PartIII-b:C/near/pins/3/4/2/2`)

Source `the November 2 reference manuscript`
lines 2671-2689. Assembles the three leaves `outerScaled`, `outerPairIter`, `outerVelJoint`
through `outerDict_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem outerDict : OuterDict :=
  outerDict_of outerScaled outerPairIter outerVelJoint

end UnforcedLeray.Short.PartIIIb.NearInst
