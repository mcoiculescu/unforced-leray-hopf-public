import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.GradLiftPairZero

/-!
# `PepsLerayInvisible` (task `PartIII-b:C/near/pins/3/3`)

Composes the two proved leaves `pairFunctional` (task `3/3/1`) and `gradLiftPairZero`
(task `3/3/2`) through `pepsLerayInvisible_of` (`Sub/PartIII-b_C_near_pins_3_3.lean`).
Source 1675-1677, 1339-1362, 4139-4146.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem pepsLerayInvisible : PepsLerayInvisible :=
  pepsLerayInvisible_of pairFunctional gradLiftPairZero

end UnforcedLeray.Short.PartIIIb.NearInst
