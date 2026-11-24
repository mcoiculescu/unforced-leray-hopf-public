import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEHess
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GradL2pIBP.Main

/-!
# `GEGradL2p` (source 2531, 1515-1531)

Task `PartIII-b:C/ward/12/3/1/2/3`.  Source of record
`the November 2 reference manuscript`, line 2531.

`gEGradL2p` composes the proved `gEHess` (`D²w ∈ Y_p`) with the phase-space integration-by-parts
inequality `gradL2pIBP`, via `gradL2p_of_hess` (`GradL2pIBP.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`GEGradL2p`** (source 2531): `‖Dw‖²_{Y_{2p}} ≤ C‖w‖_∞‖D²w‖_{Y_p}`, each `D_jw` in `L^{2p}`. -/
theorem gEGradL2p : GEGradL2p :=
  gradL2p_of_hess gEHess gradL2pIBP

end UnforcedLeray.Short.PartIIIb.Concrete
