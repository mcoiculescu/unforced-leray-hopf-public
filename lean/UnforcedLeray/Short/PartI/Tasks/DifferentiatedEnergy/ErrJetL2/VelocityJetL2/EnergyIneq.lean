import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.SliceWordReg
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.CutoffJetContinuous
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.CutoffJetHasDeriv
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.VortWordEquation
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.ViscousBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.TransportBound

/-!
# Part I, task `PartI:T08/2/2/2` (`VortJetEnergyIneq`): assembly

Source of record: `the November 2 reference manuscript`, lines 276-288.
Feeds the six leaves into the conditional theorem `vortJetEnergyIneq_of`
(`Sub/PartI_T08_2_2/EnergyIneq.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- **`VortJetEnergyIneq` (Part I, task `PartI:T08/2/2/2`).** Assembled from the six leaf
proofs via the conditional theorem `vortJetEnergyIneq_of`. -/
theorem vortJetEnergyIneq_proof : UnforcedLeray.Short.PartI.VortJetEnergyIneq :=
  vortJetEnergyIneq_of sliceWordReg_proof cutoffJetContinuous_proof cutoffJetHasDeriv_proof
    vortWordEquation_proof cutoffJetViscousBound_proof cutoffJetTransportBound_proof

end UnforcedLeray.Short.PartI
