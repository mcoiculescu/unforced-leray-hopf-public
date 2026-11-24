import UnforcedLeray.Short.PartI.Sub.PartI_T08_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.WordBounded
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcPeriodic

/-!
# Part I, task `PartI:T08/1` (`trainErrBasic_proof`): assembly

Source: `the November 2 reference manuscript` lines 261-294 and 326-329.
Assembles `trainErrBasic_of` (in `Sub/PartI_T08_1.lean`) with the three leaves
`trainWordBounded_proof` (`PartI:T08/1/1`), `qcSmooth_proof` (`PartI:T08/1/2`) and
`qcPeriodic_proof` (`PartI:T08/1/3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem trainErrBasic_proof : UnforcedLeray.Short.PartI.TrainErrBasic :=
  trainErrBasic_of trainWordBounded_proof qcSmooth_proof qcPeriodic_proof

end UnforcedLeray.Short.PartI
