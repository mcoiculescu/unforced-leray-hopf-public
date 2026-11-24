import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3_2_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2.PairWithLift.VelPhysDict
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2.PairWithLift.PhaseTestSplit
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2.PairWithLift.PhaseIntScale

/-!
# `PairWithLift` (task `PartIII-b:C/near/pins/3/2/2`)

Source `the November 2 reference manuscript` 1339-1362, 4139-4146, 2666-2668, 2683.

Assembles the three leaves `VelPhysDict` (pointwise dictionary), `PhaseTestSplit` (test
transport) and `PhaseIntScale` (change of variables in the phase integral) through the
reduction `pairWithLift_of` of the Sub file.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem pairWithLift : PairWithLift :=
  pairWithLift_of velPhysDict phaseTestSplit phaseIntScale

end UnforcedLeray.Short.PartIIIb.NearInst
