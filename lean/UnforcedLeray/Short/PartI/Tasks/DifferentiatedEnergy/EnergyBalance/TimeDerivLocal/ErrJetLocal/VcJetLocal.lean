import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrJetLocal.VcJetLocal.Late

/-!
# Part I, task `PartI:T08/4/1/1/1/1` (`VcJetLocalL2`): time-local `L²` bound for `V_c`

Source: `the November 2 reference manuscript` line 294 (`V_c^p`) and lines 326-329.

The target follows from the window lemma `vcJetLocalL2_of_late` (Sub/PartI_T08_4_1_1_1_1.lean)
and the late-age leaf `vcJetLocalLate_proof` (VcJetLocal/Late.lean).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- Time-local `L²(cell)` bound for `V_c` (task `PartI:T08/4/1/1/1/1`). -/
theorem vcJetLocalL2_proof : UnforcedLeray.Short.PartI.VcJetLocalL2 :=
  UnforcedLeray.Short.PartI.vcJetLocalL2_of_late UnforcedLeray.Short.PartI.vcJetLocalLate_proof

end UnforcedLeray.Short.PartI
