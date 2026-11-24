import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Window.GradL2Quant
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VelJetLocal.Window.LocalBoundsBUC

/-!
# Part I, task `PartI:T08/4/1/1/1/2/1` (`VelJetLocalWindow`): window leaf

Source: `the November 2 reference manuscript` lines 261-288.

The target is the time-local `L²` bound at ages `width ν s < c²`. It follows from the two leaves
`TrainLocalBoundsBUC` (proved by `trainLocalBoundsBUC_proof`, `Window/LocalBoundsBUC.lean`) and
`GradL2Quant` (proved by `gradL2Quant_proof`, `Window/GradL2Quant.lean`), via the conditional
`velJetLocalWindow_of` in `Sub/PartI_T08_4_1_1_1_2_1.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **`VelJetLocalWindow`** (proved, lines 261-288): assembly of the proved leaves
`trainLocalBoundsBUC_proof` and `gradL2Quant_proof` through `velJetLocalWindow_of`. -/
theorem velJetLocalWindow_proof : UnforcedLeray.Short.PartI.VelJetLocalWindow :=
  velJetLocalWindow_of trainLocalBoundsBUC_proof gradL2Quant_proof

end UnforcedLeray.Short.PartI
