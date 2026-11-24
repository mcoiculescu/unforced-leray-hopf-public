import UnforcedLeray.Short.PartIIb.Sub.T15_2_10
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogTranslateContinuous
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogAvgConverges.Slice
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogAvgConverges.AEMeas
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.ProductRule.LogAvgConverges.CS

/-!
# Part II-b, task `PartII-b:T15/2/10`: `LogAvgConverges` assembled from its three leaves

Source: `the November 2 reference manuscript`, lines 1975-1979.
Applies the assembly `logAvgConverges_of` (`Sub/T15_2_10.lean`) to the three leaf proofs
`logAcSlice`, `logAcAEMeas`, `logAcCS` (folder `LogAvgConverges/`) and to `logTranslateContinuous`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T15/2/10`**: the difference quotient of `G` converges to `G` in `L²(logMeas c)`. -/
theorem logAvgConverges : UnforcedLeray.Short.IIb.LogAvgConverges :=
  logAvgConverges_of logAcSlice logAcAEMeas logAcCS logTranslateContinuous

end UnforcedLeray.Short.IIb
