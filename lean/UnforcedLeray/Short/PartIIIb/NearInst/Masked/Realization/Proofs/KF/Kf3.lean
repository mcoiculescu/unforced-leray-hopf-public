import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.SubKF3
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresSmooth
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.PresDecay
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.GradOrth
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.SolSlice
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.MemLpDecay
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.Slice
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.HeatDiv
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.HeatPres
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KF.KF3.FDerivK

/-!
# `kf3 : KF3` (source 3586-3601, 3617-3618)

Assembly of the nine proved top leaves `kf3PresSmooth`, `kf3PresDecay`, `kf3GradOrth`,
`kf3SolSlice`, `kf3MemLpDecay`, `kf3Slice`, `kf3HeatDiv`, `kf3HeatPres`, `kf3FDerivK` through
`kf3_of` (`SubKF3.lean`).  Source of record:
`the November 2 reference manuscript`
(lines 3586-3601, 3617-3618).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- **KF3** (3586-3601, 3617-3618): the heat-Leray identity for smooth outer tensors, assembled
from the proved leaves through `kf3_of`. -/
theorem kf3 : KF3 := kf3_of kf3PresSmooth kf3PresDecay kf3GradOrth kf3SolSlice kf3MemLpDecay
  kf3Slice kf3HeatDiv kf3HeatPres kf3FDerivK

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
