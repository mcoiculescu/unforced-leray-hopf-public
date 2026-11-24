import UnforcedLeray.Short.PartI.Sub.T02_3_11
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.SliceSmooth
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.DiffEnergy
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.DiffMomentum
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.StretchPointwise
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.Continuity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.IntegrandDecomp
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.ViscousEstimate
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.TransportIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.TransportEstimate
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.StretchEstimate
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.PressureIdentity
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.ClassicalCutoffEnergyIneq.PressureEstimate

/-!
# Part I, task `PartI:T02/3/11`: unconditional `ClassicalCutoffEnergyIneq`

Source of record: `the November 2 reference manuscript`, lines 276-288.

The conditional theorem `classicalCutoffEnergyIneq_of` (`Sub/T02_3_11.lean`) derives
`ClassicalCutoffEnergyIneq` (`Sub/T02_3.lean`, line 195) from ten leaf statements. This file supplies
each leaf from its proved module, together with the transverse cutoff facts `EtaCutoffFacts`
(`Tasks/ClassicalOdd/EtaCutoffFacts.lean`) and the cell toolkit `cellToolkit`
(`Tasks/TrainCutoffEnergyProof/CellToolkit.lean`). The four auxiliary statements `CcSliceSmooth`,
`CcDiffEnergyBound`, `CcStretchPointwise`, `CcDiffMomentum` are proved in their own leaf modules.
-/

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T02/3/11`, unconditional form**: `ClassicalCutoffEnergyIneq` holds. -/
theorem classicalCutoffEnergyIneq : ClassicalCutoffEnergyIneq := by
  have hη : EtaCutoffFacts := etaCutoffFacts
  have hI : CellIntegrableOfSupport := cellToolkit.1
  have hZ : CellDerivZero := cellToolkit.2
  have hS : CcSliceSmooth := ccSliceSmooth
  have hE : CcDiffEnergyBound := ccDiffEnergyBound hS
  have hP : CcStretchPointwise := ccStretchPointwise hS
  have hM : CcDiffMomentum := ccDiffMomentum hS
  exact classicalCutoffEnergyIneq_of ccEnergyContinuous ccEnergyHasDeriv
    (ccIntegrandDecomp hI hS hM) (ccViscousIdentity hη hI hZ hS) (ccViscousEstimate hη hI hS hE)
    (ccTransportIdentity hη hI hZ hS) (ccTransportEstimate hη hI hS hE)
    (ccStretchEstimate hI hS hP) (ccPressureIdentity hη hI hZ hS) (ccPressureEstimate hη hI hS hE)

example : ClassicalCutoffEnergyIneq := classicalCutoffEnergyIneq

end UnforcedLeray.Short.PartI
