import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_6
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.PressureGradLocal.Quant
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.PressureGradLocal.Q0
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.PressureGradLocal.Q1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.PressureGradLocal.Q2

/-!
# Part I, task `PartI:T08/4/1/1/6` (`TrainPressureGradLocal`): assembly

Source: `the November 2 reference manuscript` lines 266-270, 326-329.
Composes the leaves Q0, Q1, Q2 and the quantitative estimate `pressureGradJetL2Quant_proof_of`
with `trainPressureGradLocal_of_quant`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem trainPressureGradLocal_of (h1 : UnforcedLeray.Short.PartI.TrainAdvLocal)
    (h2 : UnforcedLeray.Short.PartI.TrainStressDivLocal) :
    UnforcedLeray.Short.PartI.TrainPressureGradLocal :=
  trainPressureGradLocal_of_quant
    (pressureGradJetL2Quant_proof_of pressureGradOrder0Quant_proof gradL2QuantP_proof
      pressureGradWordLapId_proof) h1 h2

end UnforcedLeray.Short.PartI
