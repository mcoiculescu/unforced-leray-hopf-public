import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderUL4
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderCore
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderEvol

/-!
# `PartII-b:B3`: `BallHeatRemainder`

Assembles `ballHeatRemainder_proof` from `B3Stmt.ballHeatRemainder_of`,
`ballHeatRemainder_UL4`, `ballHeatRemainder_Core`, and `ballHeatRemainder_Evol`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem ballHeatRemainder_proof : UnforcedLeray.Short.IIb.BallHeatRemainder :=
  B3Stmt.ballHeatRemainder_of ballHeatRemainder_UL4 ballHeatRemainder_Core ballHeatRemainder_Evol

end UnforcedLeray.Short.IIb
