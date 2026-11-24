import UnforcedLeray.Short.PartI.Sub.PartI_T25_3
import UnforcedLeray.Lib.Train.VortexBounds
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.PressAgeJet.Unweighted.QcDiv
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.PressAgeJet.Unweighted.AdvDiff

/-!
# `PartI:T25/3/2` (`TrainFixedBandPressAgeJetUnweighted`)

Source of record: `the November 2 reference manuscript`, lines 468-478, 543-551.

Proves `TrainFixedBandPressAgeJetUnweighted` by combining `trainFixedBandQcDivAgeJet_proof`
(`Unweighted/QcDiv.lean`) and `trainFixedBandAdvDiffStep_proof` (`Unweighted/AdvDiff.lean`)
with `trainFixedBandPressAgeJetUnweighted_of_qc_adv` (`Sub/PartI_T25_3.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- Proof of `TrainFixedBandPressAgeJetUnweighted` (`PartI:T25/3/2`). -/
theorem trainFixedBandPressAgeJetUnweighted_proof : TrainFixedBandPressAgeJetUnweighted :=
  trainFixedBandPressAgeJetUnweighted_of_qc_adv
    trainFixedBandQcDivAgeJet_proof
    trainFixedBandAdvDiffStep_proof

end UnforcedLeray.Short.PartI
