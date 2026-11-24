import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VcJetLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal

/-!
# Part I, task `PartI:T08/4/1/1/1` (`TrainErrJetLocalL2`): assembly

Source `the November 2 reference manuscript` lines 261-288, 326-329.

`TrainErrJetLocalL2` follows from the conditional reduction `trainErrJetLocalL2_of`
(in `Sub/PartI_T08_4_1_1_1`) and the two leaves `vcJetLocalL2_proof` (`VcJetLocal`) and
`velJetLocalL2_proof` (`VelJetLocal`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:T08/4/1/1/1`:** `TrainErrJetLocalL2`, from the two leaves. -/
theorem trainErrJetLocalL2_proof : UnforcedLeray.Short.PartI.TrainErrJetLocalL2 :=
  trainErrJetLocalL2_of vcJetLocalL2_proof velJetLocalL2_proof

end UnforcedLeray.Short.PartI
