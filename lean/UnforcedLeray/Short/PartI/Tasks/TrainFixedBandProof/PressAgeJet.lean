import UnforcedLeray.Short.PartI.Sub.PartI_T25_3
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.PressAgeJet.PcTwoMulM
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.PressAgeJet.Unweighted

/-!
# `PartI:T25/3`: Fixed-band pressure-gradient age-jet bounds (`TrainFixedBandPressAgeJet`)

Source of record: `the November 2 reference manuscript`, lines 468–478, 543–551.

Assembles `TrainFixedBandPressAgeJet` from `trainFixedBandPcAgeJetTwoMulM_proof` (`PartI:T25/3/1`)
and `trainFixedBandPressAgeJetUnweighted_proof` (`PartI:T25/3/2`) via
`trainFixedBandPressAgeJet_of_leaves`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- Proof of `TrainFixedBandPressAgeJet` (`PartI:T25/3`) from
`TrainStreamVelocityPressureTails`, `TrainFluctuationDecay`, and `TrainFixedBandVelAgeJet`. -/
theorem trainFixedBandPressAgeJet_of
    (hTails : TrainStreamVelocityPressureTails)
    (hFD : TrainFluctuationDecay)
    (hVel : TrainFixedBandVelAgeJet) :
    TrainFixedBandPressAgeJet :=
  trainFixedBandPressAgeJet_of_leaves
    trainFixedBandPcAgeJetTwoMulM_proof
    trainFixedBandPressAgeJetUnweighted_proof
    hTails hFD hVel

end UnforcedLeray.Short.PartI

end
