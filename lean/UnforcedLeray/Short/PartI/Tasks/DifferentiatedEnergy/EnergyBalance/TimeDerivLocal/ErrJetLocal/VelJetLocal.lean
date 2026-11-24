import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Window
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Late

/-!
# Part I, task `PartI:T08/4/1/1/1/2` (`VelJetLocalL2`): assembly

Source: `the November 2 reference manuscript` lines 261-288 and 326-329.

`VelJetLocalL2` follows from the window leaf `velJetLocalWindow_proof` and the late leaf
`velJetLocalLate_proof` via `velJetLocalL2_of` (in `Sub/PartI_T08_4_1_1_1_2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:T08/4/1/1/1/2`:** `VelJetLocalL2`, from the window and late leaves. -/
theorem velJetLocalL2_proof : VelJetLocalL2 :=
  velJetLocalL2_of velJetLocalWindow_proof velJetLocalLate_proof

end UnforcedLeray.Short.PartI
