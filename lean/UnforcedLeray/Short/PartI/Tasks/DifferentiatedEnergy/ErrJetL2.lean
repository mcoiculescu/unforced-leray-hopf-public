import UnforcedLeray.Short.PartI.Sub.PartI_T08_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VcWordL2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2

/-!
# Part I, task `PartI:T08/2` (`TrainErrJetL2`): proof

Source: `the November 2 reference manuscript` lines 261-288, 294, 344.
Assembles the two leaves `vcWordL2_proof` (`PartI:T08/2/1`) and `trainVelocityJetL2_proof`
(`PartI:T08/2/2`) into the conditional theorem `trainErrJetL2_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- **`TrainErrJetL2` (Part I, task `PartI:T08/2`).** From the two leaf proofs via
`trainErrJetL2_of`. -/
theorem trainErrJetL2_proof : UnforcedLeray.Short.PartI.TrainErrJetL2 :=
  trainErrJetL2_of vcWordL2_proof trainVelocityJetL2_proof

end UnforcedLeray.Short.PartI
