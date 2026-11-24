import UnforcedLeray.Short.PartI.Sub.PartI_T25
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VelAgeJet
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.VortAgeJet
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof.PressAgeJet

/-!
# `PartI:T25`: fixed-band comparison for `(v - V_c^p, ω - curl V_c^p, ∇(p - p_c^p))` (`sct:fixed-band`)

Source of record: `the November 2 reference manuscript`, lines 468-478, 541-551.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- Proof of `TrainFixedBand` (`PartI:T25`, `sct:fixed-band`, source lines 468-478, 541-551)
assembled from `trainFixedBandVelAgeJet_of` (`PartI:T25/1`), `trainFixedBandVortAgeJet_of`
(`PartI:T25/2`), and `trainFixedBandPressAgeJet_of` (`PartI:T25/3`). -/
theorem trainFixedBand_proof (hTails : TrainStreamVelocityPressureTails) (hFD : TrainFluctuationDecay) : TrainFixedBand := by
  let hVel := trainFixedBandVelAgeJet_of hTails hFD
  exact trainFixedBand_of hTails hFD hVel
    (trainFixedBandVortAgeJet_of hTails hFD hVel)
    (trainFixedBandPressAgeJet_of hTails hFD hVel)

end UnforcedLeray.Short.PartI
