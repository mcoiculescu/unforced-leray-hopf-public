import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.PressAgeJet.Unweighted.AdvDiff

/-!
# `Short/PartI/Tasks/TrainFixedBandProof/VelAgeJet/AdvDiff.lean` — Task `PartI:T25/1/2`

Source of record: `the November 2 reference manuscript`, lines 326–336, 468–478,
541–551.

Re-exports `UnforcedLeray.Short.PartI.trainFixedBandAdvDiffStep_proof : TrainFixedBandAdvDiffStep`
proved in `UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.PressAgeJet.Unweighted.AdvDiff`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

namespace VelAgeJet

/-- Proof of `TrainFixedBandAdvDiffStep` (`PartI:T25/1/2`). -/
theorem trainFixedBandAdvDiffStep_proof : TrainFixedBandAdvDiffStep :=
  UnforcedLeray.Short.PartI.trainFixedBandAdvDiffStep_proof

end VelAgeJet

end UnforcedLeray.Short.PartI
