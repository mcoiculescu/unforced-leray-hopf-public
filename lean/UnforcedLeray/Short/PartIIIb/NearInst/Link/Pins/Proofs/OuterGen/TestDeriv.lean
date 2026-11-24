import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_3_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.PairTransC
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.PairDilN
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.PairHeatC
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.TransposeDeriv
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Scaling

/-!
# `outerTestDeriv` (task `PartIII-b:C/near/pins/3/4/2/3/2`)

Source `the November 2 reference manuscript` lines 1339-1362, 3346-3352, 4139-4146.
Assembly of the five leaves (transposition of the three factors, transposition of `S_ε(t)`,
strong `t`-derivative on a scaled test, scaling identity) through `outerTestDeriv_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem outerTestDeriv : OuterTestDeriv :=
  outerTestDeriv_of (outerTransposePair_of outerPairTransC outerPairDilN outerPairHeatC)
    outerTransposeDeriv outerScaling

end UnforcedLeray.Short.PartIIIb.NearInst
