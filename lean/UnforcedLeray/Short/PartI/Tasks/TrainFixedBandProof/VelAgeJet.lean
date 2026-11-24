import UnforcedLeray.Short.PartI.Sub.PartI_T25_1
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.QcDiv_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.AdvDiff_Aux
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet.PressStep_Aux

/-!
# `Short/PartI/Tasks/TrainFixedBandProof/VelAgeJet.lean` — Task `PartI:T25/1`

Source of record: `the November 2 reference manuscript`, lines 468–478, 541–551.

Assembles `trainFixedBandVelAgeJet_of` from `trainFixedBandVelAgeJet_of_leaves` and the three
forcing leaves `trainFixedBandQcDivAgeJet_proof`, `trainFixedBandAdvDiffStep_proof`, and
`trainFixedBandPressStep_of_tails` via cycle-free helpers in `VelAgeJet/`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- Proof of `TrainFixedBandVelAgeJet` (`PartI:T25/1`) from `TrainStreamVelocityPressureTails`
and `TrainFluctuationDecay`. -/
theorem trainFixedBandVelAgeJet_of (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay) : TrainFixedBandVelAgeJet :=
  trainFixedBandVelAgeJet_of_leaves hTails hFD
    VelAgeJetAux.trainFixedBandQcDivAgeJet_proof
    VelAgeJetAux.trainFixedBandAdvDiffStep_proof
    (VelAgeJetAux.trainFixedBandPressStep_of_tails hTails)

end UnforcedLeray.Short.PartI

end
