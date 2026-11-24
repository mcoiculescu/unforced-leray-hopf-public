import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctionalDual
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.GenAdjointPair

/-!
# `RepsVecEquation` (task `PartIII-b:C/near/pins/3/4`)

Composes the three proved leaves `pairFunctional` (task `3/3/1`), `pairFunctionalDual`
(task `3/4/1`) and `genAdjointPair` (task `3/4/2`) through `repsVecEquation_of`
(`Sub/PartIII-b_C_near_pins_3_4.lean`).
Source 1339-1362, 1675-1677, 4139-4146.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem repsVecEquation : RepsVecEquation :=
  repsVecEquation_of pairFunctional pairFunctionalDual genAdjointPair

end UnforcedLeray.Short.PartIIIb.NearInst
