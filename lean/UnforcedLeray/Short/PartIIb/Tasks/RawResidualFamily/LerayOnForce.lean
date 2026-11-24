import UnforcedLeray.Short.PartIIb.Sub.R1_3
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.LerayOnForce.CTranspose
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.LerayOnForce.SolSliceFixed

/-!


Target `UnforcedLeray.Short.IIb.LerayOnForce` (`Sub/R1.lean`).
Source of record: `the November 2 reference manuscript`, lines 2519-2524;
`paper/main.tex` lines 5085 and 5385.

The conditional theorem `lerayOnForce_of` (`Sub/R1_3.lean`) takes the two slice-level leaves
`LerayCTranspose` (`LerayOnForce/CTranspose.lean`) and `SolSliceFixed`
(`LerayOnForce/SolSliceFixed.lean`). This file supplies both leaves and applies it.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:R1/3`: the Leray projection on the force space.** -/
theorem lerayOnForce_proof : UnforcedLeray.Short.IIb.LerayOnForce :=
  lerayOnForce_of lerayCTranspose solSliceFixed

end UnforcedLeray.Short.IIb
