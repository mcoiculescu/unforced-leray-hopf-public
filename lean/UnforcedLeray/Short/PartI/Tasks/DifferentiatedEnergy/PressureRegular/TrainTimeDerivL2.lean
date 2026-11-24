import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.PcSmoothDecay
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainErrLaplacianL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainAdvDiffL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainStressDivL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainTimeDerivL2.ErrPressureGradJetL2

/-!
# Part I, task `PartI:T08/3/3` (`TrainTimeDerivL2`): assembly

Source: `the November 2 reference manuscript` lines 261-288 and 326-336.

The unconditional target is obtained by applying the reduction `trainTimeDerivL2_of` to the
five proved leaves: `PcSmoothDecay`, `TrainErrLaplacianL2`, `TrainAdvDiffL2`, `TrainStressDivL2`
and `ErrPressureGradJetL2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem trainTimeDerivL2_proof : UnforcedLeray.Short.PartI.TrainTimeDerivL2 :=
  trainTimeDerivL2_of pcSmoothDecay_proof trainErrLaplacianL2_proof trainAdvDiffL2_proof
    trainStressDivL2_proof errPressureGradJetL2_proof

end UnforcedLeray.Short.PartI
