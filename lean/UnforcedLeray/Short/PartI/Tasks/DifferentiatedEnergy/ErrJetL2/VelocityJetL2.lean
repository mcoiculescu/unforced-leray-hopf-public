import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.DatumWordL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.CutoffL2OfBound
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.GradL2OfLapL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.VelocityWordLap

/-!
# Part I, task `PartI:T08/2/2` (`TrainVelocityJetL2`): assembly

Source of record: `the November 2 reference manuscript`, lines 261-288.
Feeds the five leaf proofs (and the proved `cutoffGronwall_proof` of `Sub/PartI_T08_2_2.lean`)
into the conditional theorem `trainVelocityJetL2_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- **`TrainVelocityJetL2` (Part I, task `PartI:T08/2/2`).** Assembled from the five leaf
proofs and `cutoffGronwall_proof` via the conditional theorem `trainVelocityJetL2_of`. -/
theorem trainVelocityJetL2_proof : UnforcedLeray.Short.PartI.TrainVelocityJetL2 :=
  trainVelocityJetL2_of trainDatumWordL2_proof vortJetEnergyIneq_proof cutoffGronwall_proof
    cutoffL2OfBound_proof gradL2OfLapL2_proof trainVelocityWordLap_proof

end UnforcedLeray.Short.PartI
