import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.Pressure
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformCutoffQ

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3` (`VelZeroUniformL2`): assembly

Source of record: `the November 2 reference manuscript` lines 261-288.

`velZeroUniformL2_of` (in `Sub/PartI_T08_4_1_1_1_2_2_1_3`) reduces `VelZeroUniformL2` to the
leaves `TrainPressureBounded` (`trainPressureBounded_proof`), `VelCutoffEnergyIneq`
(`velCutoffEnergyIneq_proof`) and `CutoffL2BoundQ` (`cutoffL2BoundQ_proof`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:T08/4/1/1/1/2/2/1/3`:** `VelZeroUniformL2`, from the three leaves. -/
theorem velZeroUniformL2_proof : UnforcedLeray.Short.PartI.VelZeroUniformL2 :=
  velZeroUniformL2_of trainPressureBounded_proof velCutoffEnergyIneq_proof cutoffL2BoundQ_proof

end UnforcedLeray.Short.PartI
