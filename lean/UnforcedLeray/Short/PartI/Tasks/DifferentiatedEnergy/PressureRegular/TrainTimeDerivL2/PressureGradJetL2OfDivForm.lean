import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.PressureGradOrder0
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.GradL2OfLapL2NoBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.PressureGradWordLapL2

/-!
# Part I, task `PartI:T08/3/3/1` (`PressureGradJetL2OfDivForm`): assembly

Source of record: `the November 2 reference manuscript` lines 326-336 and 261-288.
Assembles the three leaf proofs `pressureGradOrder0_proof`, `gradL2OfLapL2NoBound_proof` and
`pressureGradWordLapL2_proof` through `pressureGradJetL2OfDivForm_of` (in `Sub/PartI_T08_3_3_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem pressureGradJetL2OfDivForm_proof : PressureGradJetL2OfDivForm :=
  pressureGradJetL2OfDivForm_of pressureGradOrder0_proof gradL2OfLapL2NoBound_proof
    pressureGradWordLapL2_proof

end UnforcedLeray.Short.PartI
