import UnforcedLeray.Short.PartI.Sub.PartI_T23
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.StressMomentsAllOrders
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.RemainderLpBound
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansion.StreamLpBound

/-!
# `TrainMeanExpansion` (`PartI:T23`)

Source of record: `the November 2 reference manuscript`, lines 447-462 and
528-540, Lemma `sct:expansion`.

Assembles `TrainMeanExpansion` from `trainMeanExpansion_of` (`Sub/PartI_T23.lean`) and the three
leaf theorems:
* `trainMeanStressMomentsAllOrders_proof` (`PartI:T23/1`),
* `trainMeanRemainderLpBound_proof` (`PartI:T23/2`),
* `trainMeanStreamLpBound_proof` (`PartI:T23/3`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Main theorem (`PartI:T23`)**: heat-kernel expansion and remainder bounds for the mean stream
(`sct:expansion`, source lines 447-462 and 528-540). -/
theorem trainMeanExpansion_proof (hTails : TrainStreamVelocityPressureTails) (hFD : TrainFluctuationDecay) (hMP : OverlapMeanPrimitive) : TrainMeanExpansion := by
  exact trainMeanExpansion_of hTails (trainMeanStressMomentsAllOrders_proof hTails hFD) (trainMeanRemainderLpBound_proof hTails hFD hMP) (trainMeanStreamLpBound_proof hTails hFD hMP)

end UnforcedLeray.Short.PartI
