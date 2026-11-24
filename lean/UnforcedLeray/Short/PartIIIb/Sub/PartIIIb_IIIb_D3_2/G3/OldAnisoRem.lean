import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoRemOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput.Tail.TrainVelTail
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput.Tail.FlowKcCore
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.LaterOutput.Tail.FlowKcImpulse

/-!
# `PartIII-b:IIIb-D3/2/G3/1/3`: `LaterOutputAbsOp` and `LaterOutputRem` from the tail bounds

Source of record: `the November 2 reference manuscript`
lines 4440-4457, 4509-4518, 3272-3289.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

/-- Absolute later-output operator bound `G3.LaterOutputAbsOp D` from `TrainL2Decay`,
`FullClockLongForward`, and `CTKineticImpulse` (source lines 4440-4457, 3272-3289). -/
theorem laterOutputAbsOp_of (D : SeqData)
    (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay)
    (hL : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    G3.LaterOutputAbsOp D :=
  laterOutputAbsOp_of_parts D
    (G1.LaterOutput.trainVelTailBound_of D hL2)
    (G1.LaterOutput.unforcedFlowKcCoreBound_of D hL)
    (G1.LaterOutput.unforcedFlowKcImpulseBound_of D hL hKI)

/-- Old anisotropic remainder later-output bound `G3.LaterOutputRem D` from `TrainL2Decay`,
`FullClockLongForward`, and `CTKineticImpulse` (source lines 4440-4457, 4509-4518, 3272-3289). -/
theorem laterOutputRem_of (D : SeqData)
    (hL2 : UnforcedLeray.Short.PartI.TrainL2Decay)
    (hL : UnforcedLeray.Short.IIIa.FullClockLongForward)
    (hKI : UnforcedLeray.Short.IIIa.CTKineticImpulse) :
    G3.LaterOutputRem D :=
  laterOutputRem_of_laterOutputAbsOp D (laterOutputAbsOp_of D hL2 hL hKI)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

end
