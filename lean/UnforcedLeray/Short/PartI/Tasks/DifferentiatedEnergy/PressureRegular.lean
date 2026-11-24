import UnforcedLeray.Short.PartI.Sub.T08_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.PcSmoothDecay
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.PeriodicDecayBounded
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainAdvDiffL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainErrLaplacianL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainStressDivL2

/-!
# Part I, task `PartI:T08/3` (`TrainPressureRegular`): assembly

Source: `the November 2 reference manuscript` lines 266-270 and 326-329.

The unconditional target is obtained by applying the reduction `trainPressureRegular_of` to the
six proved leaves: `PcSmoothDecay`, `PeriodicDecayBounded`, `TrainTimeDerivL2`, `TrainAdvDiffL2`,
`TrainErrLaplacianL2` and `TrainStressDivL2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem trainPressureRegular_proof : UnforcedLeray.Short.PartI.TrainPressureRegular :=
  trainPressureRegular_of pcSmoothDecay_proof periodicDecayBounded_proof trainTimeDerivL2_proof
    trainAdvDiffL2_proof trainErrLaplacianL2_proof trainStressDivL2_proof

end UnforcedLeray.Short.PartI
