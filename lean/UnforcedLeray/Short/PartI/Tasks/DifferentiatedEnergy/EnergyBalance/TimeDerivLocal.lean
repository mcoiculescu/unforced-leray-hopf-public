import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrSupLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.LapLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.AdvLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.StressDivLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.PressureGradLocal

/-!
# Part I, task `PartI:T08/4/1/1` (`TrainTimeDerivLocalL2`): proof

Source `the November 2 reference manuscript` lines 261-288, 326-329.
Composes the decomposition `trainTimeDerivJetLocalAllAges_of` with the six leaf proofs
`trainErrJetLocalL2_proof`, `trainErrSupLocal_proof`, `trainLapLocal_of_err`,
`trainAdvLocal_of`, `trainStressDivLocal_proof` and `trainPressureGradLocal_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainTimeDerivLocalL2_proof :
    UnforcedLeray.Short.PartI.TrainTimeDerivLocalL2 :=
  UnforcedLeray.Short.PartI.trainTimeDerivLocalL2_of
    (UnforcedLeray.Short.PartI.trainTimeDerivJetLocalAllAges_of
      (UnforcedLeray.Short.PartI.trainLapLocal_of_err
        UnforcedLeray.Short.PartI.trainErrJetLocalL2_proof)
      (UnforcedLeray.Short.PartI.trainAdvLocal_of
        UnforcedLeray.Short.PartI.trainErrJetLocalL2_proof
        UnforcedLeray.Short.PartI.trainErrSupLocal_proof)
      (UnforcedLeray.Short.PartI.trainPressureGradLocal_of
        (UnforcedLeray.Short.PartI.trainAdvLocal_of
          UnforcedLeray.Short.PartI.trainErrJetLocalL2_proof
          UnforcedLeray.Short.PartI.trainErrSupLocal_proof)
        UnforcedLeray.Short.PartI.trainStressDivLocal_proof)
      UnforcedLeray.Short.PartI.trainStressDivLocal_proof)

end UnforcedLeray.Short.PartI
