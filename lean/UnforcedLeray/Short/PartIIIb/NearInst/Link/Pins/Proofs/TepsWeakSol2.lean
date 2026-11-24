import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Sub.PartIIIb_C_near_pins_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2.PepsRealMember
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.TepsWeakSol2.PairWithLift

/-!
# `PepsSolenoidal` (task `PartIII-b:C/near/pins/3/2`)

Source `the November 2 reference manuscript` 1675-1677, 1339-1362, 4139-4146.

Assembles the two leaves `PepsRealMember` (real part of `P_ε z` is solenoidal in `H`) and
`PairWithLift` (physical pairing with the lift) through the reduction `pepsSolenoidal_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem pepsSolenoidal : PepsSolenoidal :=
  pepsSolenoidal_of pepsRealMember pairWithLift

end UnforcedLeray.Short.PartIIIb.NearInst
