import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.GradLiftChartRep.ChartRep
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.GradLiftChartRep.ScalarTest
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.GradLiftChartRep.Pointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.GradLiftChartRep.IBPScalar

/-!
# `GradLiftPairZero` (task `PartIII-b:C/near/pins/3/3/2`)

Composes the four leaves `gradLiftChartRep`, `gradLiftScalarTest`, `gradLiftPointwise`,
`phaseIBPScalar` through `gradLiftPairZero_of` (`Sub/PartIII-b_C_near_pins_3_3_2.lean`).
Source 1666, 1675-1677.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem gradLiftPairZero : GradLiftPairZero :=
  gradLiftPairZero_of gradLiftChartRep gradLiftScalarTest gradLiftPointwise phaseIBPScalar

end UnforcedLeray.Short.PartIIIb.NearInst
