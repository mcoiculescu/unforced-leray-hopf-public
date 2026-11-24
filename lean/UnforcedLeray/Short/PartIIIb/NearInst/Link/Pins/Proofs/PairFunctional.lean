import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.ChartTransport
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.RealPairFunctional

/-!
# `PairFunctional` (task `PartIII-b:C/near/pins/3/3/1`)

Composes the two leaves `chartTransport` (`PairFunctional/ChartTransport.lean`) and
`realPairFunctional` (`PairFunctional/RealPairFunctional.lean`) through `pairFunctional_of`
(`Sub/PartIII-b_C_near_pins_3_3_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem pairFunctional : PairFunctional :=
  pairFunctional_of realPairFunctional chartTransport

end UnforcedLeray.Short.PartIIIb.NearInst
