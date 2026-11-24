import UnforcedLeray.Short.PartI.Sub.PartI_T09_5
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5.RightCont

/-!
# Part I, task `PartI:T09/5`: `TrainErrInitial`

Source of record: `the November 2 reference manuscript`, lines 261-288, 294, 341-344.

The reduction `trainErrInitial_proof_of` and the right-continuity input are proved in
`Sub/PartI_T09_5.lean`; the input `trainJetEnergyRightCont_proof` is proved in
`Sub/PartI_T09_5/RightCont.lean`. This file assembles them into `TrainErrInitial` with no hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target `PartI:T09/5`.** `TrainErrInitial` holds unconditionally. -/
theorem trainErrInitial_proof : TrainErrInitial :=
  trainErrInitial_proof_of trainJetEnergyRightCont_proof

end UnforcedLeray.Short.PartI
