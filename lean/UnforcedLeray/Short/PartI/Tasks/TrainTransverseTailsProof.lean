import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign

/-!
# `PartI:T24`: transverse tails of the train (`sct:transverse`)

Source of record: `the November 2 reference manuscript`, lines 460-467, 484-515.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainTransverseTails_proof (hVort : TrainVorticityGaussianTail) (hTails : TrainStreamVelocityPressureTails) : TrainTransverseTails :=
  trainTransverseTails_of hVort hTails

end UnforcedLeray.Short.PartI
