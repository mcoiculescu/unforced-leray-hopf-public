import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.CellToolkit
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.SliceSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.DiffEnergy
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.Continuity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.IntegrandDecomp
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.ViscousEstimate
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.TransportIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.TransportEstimate
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.StretchIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.StretchEstimate
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.PressureIdentity
import UnforcedLeray.Short.PartI.Tasks.TrainCutoffEnergyProof.PressureEstimate

/-!
# Part I, task `PartI:T05b/2`: unconditional `TrainCutoffEnergyIneq`

Source of record: `the November 2 reference manuscript`, lines 276-288.

The conditional theorem `trainCutoffEnergyIneq_of` (`Sub/T05b_2.lean`) derives
`TrainCutoffEnergyIneq` (`Sub/T05.lean`, line 170) from eleven leaf statements. This file supplies
each leaf from its proved module and the transverse cutoff facts `EtaCutoffFacts`.

`TrainUniquenessFwd` (task `PartI:T05b/1`) is not proved here.
-/

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T05b/2`, unconditional form**: `TrainCutoffEnergyIneq` holds. -/
theorem trainCutoffEnergyIneq : TrainCutoffEnergyIneq := by
  have hη : EtaCutoffFacts := etaCutoffFacts
  have hI : CellIntegrableOfSupport := cellToolkit.1
  have hZ : CellDerivZero := cellToolkit.2
  have hS : TrainSliceSmooth := trainSliceSmooth
  have hE : DiffEnergyBound := diffEnergyBound
  exact trainCutoffEnergyIneq_of cutoffEnergyContinuous cutoffEnergyHasDeriv
    (cutoffIntegrandDecomp hI hS) (viscousIdentity hη hI hZ hS) (viscousEstimate hη hI hS hE)
    (transportIdentity hη hI hZ hS) (transportEstimate hη hI hS hE)
    (stretchIdentity hη hI hZ hS) (stretchEstimate hη hI hS hE)
    (pressureIdentity hη hI hZ hS) (pressureEstimate hη hI hS hE)

end UnforcedLeray.Short.PartI
