import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late.Uniform

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2` (`VelJetLocalLate`): assembly

Source: `the November 2 reference manuscript` lines 261-288.

`VelJetLocalLate` follows from `VelJetUniformL2` (proved in `Late/Uniform.lean`) via
`velJetLocalLate_of` (in `Sub/PartI_T08_4_1_1_1_2_2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:T08/4/1/1/1/2/2`:** `VelJetLocalLate`, from the uniform leaf. -/
theorem velJetLocalLate_proof : UnforcedLeray.Short.PartI.VelJetLocalLate :=
  velJetLocalLate_of velJetUniformL2_proof

end UnforcedLeray.Short.PartI
