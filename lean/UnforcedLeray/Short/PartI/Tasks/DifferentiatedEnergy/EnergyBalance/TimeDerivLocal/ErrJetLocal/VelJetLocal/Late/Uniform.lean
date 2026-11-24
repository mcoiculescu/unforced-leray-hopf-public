import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.DatumWordL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.VelocityWordLap
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformCutoffQ
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformGradQ
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1` (`VelJetUniformL2`): assembly from the leaves

Source of record: `the November 2 reference manuscript` lines 261-288.

`velJetUniformL2_of` (in `Sub/PartI_T08_4_1_1_1_2_2_1`) reduces `VelJetUniformL2` to
`TrainDatumWordL2`, `VortJetEnergyIneq`, `TrainVelocityWordLap` (proved in the `ErrJetL2`
tasks), `CutoffL2BoundQ` (`cutoffL2BoundQ_proof`), `GradL2BoundQ` (`gradL2BoundQ_proof`) and
`VelZeroUniformL2` (`velZeroUniformL2_proof`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:T08/4/1/1/1/2/2/1`:** `VelJetUniformL2`, from the proved leaves. -/
theorem velJetUniformL2_proof : UnforcedLeray.Short.PartI.VelJetUniformL2 :=
  velJetUniformL2_of trainDatumWordL2_proof vortJetEnergyIneq_proof trainVelocityWordLap_proof
    cutoffL2BoundQ_proof gradL2BoundQ_proof velZeroUniformL2_proof

end UnforcedLeray.Short.PartI
