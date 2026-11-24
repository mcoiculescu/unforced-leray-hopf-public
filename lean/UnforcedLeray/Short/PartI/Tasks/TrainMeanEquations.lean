import UnforcedLeray.Short.PartI.Sub.T01
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.HmeanContDiff
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.TrainMeanV2
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanMomentumEta
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanEnergy
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.MeanStreamTimeDecay
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.ConstZero

/-!
# Part I, task `PartI:T01`: the mean equations `sct:mean` of the train (unconditional assembly)

Source of record: `the November 2 reference manuscript`, lines 397-404.
Assembles the conditional theorem `trainMeanEquations_of` (`Sub/T01.lean`) from the eight leaf
results `PartI:T01/1 ... T01/11`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`PartI:T01`, the mean equations of the train** (source lines 397-404). -/
theorem trainMeanEquations_proof : TrainMeanEquations :=
  trainMeanEquations_of trainStreamSmooth hmeanContDiff trainMeanV1 trainMeanV2
    trainMeanMomentumEta trainMeanEnergy trainMeanStreamTimeDecay constZeroLemma

end UnforcedLeray.Short.PartI
