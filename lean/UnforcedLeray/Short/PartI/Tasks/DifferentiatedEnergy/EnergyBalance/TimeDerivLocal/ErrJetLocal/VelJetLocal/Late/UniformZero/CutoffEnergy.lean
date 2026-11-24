import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy.Decomp
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy.ViscousIdentity
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy.ViscousEstimate
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy.TransportId
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy.TransportEst
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy.PressureId
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.UniformZero.CutoffEnergy.PressureEst

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2` (`VelCutoffEnergyIneq`): assembly

Source of record: `the November 2 reference manuscript` lines 273-288.

The seven leaf files under `CutoffEnergy/` prove the leaf propositions
`VelIntegrandDecomp`, `VelViscousIdentity`, `VelViscousEstimate`, `VelTransportIdentity`,
`VelTransportEstimate`, `VelPressureIdentity`, `VelPressureEstimate`. The conditional theorem
`velCutoffEnergyIneq_of` (in `Sub/PartI_T08_4_1_1_1_2_2_1_3_2`) assembles them into
`VelCutoffEnergyIneq`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:T08/4/1/1/1/2/2/1/3/2`:** `VelCutoffEnergyIneq`, from the seven leaves. -/
theorem velCutoffEnergyIneq_proof : UnforcedLeray.Short.PartI.VelCutoffEnergyIneq :=
  velCutoffEnergyIneq_of velIntegrandDecomp_proof velViscousIdentity_proof
    velViscousEstimate_proof velTransportIdentity_proof velTransportEstimate_proof
    velPressureIdentity_proof velPressureEstimate_proof

end UnforcedLeray.Short.PartI
