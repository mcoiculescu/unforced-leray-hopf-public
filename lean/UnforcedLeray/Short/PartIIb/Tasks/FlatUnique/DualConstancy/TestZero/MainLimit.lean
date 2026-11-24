import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.MainLimit.Bridge
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.MainLimit.Integrable
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.MainLimit.Fubini

/-!
# Part II-b, leaf `PartII-b:T11/2/2/5` (`DualMainLimit`): assembly

Source: `the November 2 reference manuscript` 1923-1927.

`DualMainLimit` follows from the three leaves `DualPerpBridge` (`MainLimit/Bridge.lean`),
`DualMainInfIntegrable` (`MainLimit/Integrable.lean`) and `DualMainFubini` (`MainLimit/Fubini.lean`)
through `dualMainLimit_of` (`Sub/PartIIb_T11_2_2_5.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem DualMainLimit_proof : UnforcedLeray.Short.IIb.DualMainLimit :=
  dualMainLimit_of dualPerpBridge_proof dualMainInfIntegrable_proof dualMainFubini_proof

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.DualMainLimit_proof
