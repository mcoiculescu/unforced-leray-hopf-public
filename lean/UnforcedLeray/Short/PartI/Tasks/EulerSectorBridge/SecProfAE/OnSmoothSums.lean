import UnforcedLeray.Short.PartI.Sub.PartI_S11_1_1
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamQ
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.StreamPsi
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.PertZero
import UnforcedLeray.Short.PartI.Tasks.EulerSectorBridge.SecProfAE.OnSmoothSums.Bridge

/-!
# Part I, task `PartI:S11/1/1`: `secAEOnSmoothSums`

Source of record: `the November 2 reference manuscript`, lines 841-889.
Proof: `secAEOnSmoothSums_of` applied to the four leaves `secStreamQ`, `secStreamPsi`,
`secPertZero`, `secAEBridge`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

theorem secAEOnSmoothSums : SecAEOnSmoothSums :=
  secAEOnSmoothSums_of secStreamQ secStreamPsi secPertZero secAEBridge

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.secAEOnSmoothSums
