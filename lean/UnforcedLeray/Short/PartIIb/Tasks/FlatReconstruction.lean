import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F9
import UnforcedLeray.Short.PartIIb.Tasks.FlatReconstruction.FreeInteraction
import UnforcedLeray.Short.PartIIb.Tasks.FlatReconstruction.FlatColumnBound
import UnforcedLeray.Short.PartIIb.Tasks.FlatReconstruction.GlobalIdentity

/-!
# Part II-b, task `PartII-b:F9`: Global flat reconstruction (`FlatReconstruction`, SP 2313–2341)

Source of record: `the November 2 reference manuscript` (SP), lines 2313–2341,
display `short-bg:flat-reconstruction` at line 2326:
  `b_0 + z = Eα + T_0 f,   f = F - s B_v(b_0 + z) - s(∂_s - νΔ)Eα`.

Assembles `flatReconstruction_of` from `flatReconstruction_of_leaves` and the three proved leaves
`PartII-b:F9/1` (`flatFreeInteractionStep_proof`), `PartII-b:F9/2` (`flatColumnHpStep_proof`),
and `PartII-b:F9/3` (`flatReconstructionIdentityStep_proof`).
-/

namespace UnforcedLeray.Short.IIb

theorem flatReconstruction_of
    (hGE : UnforcedLeray.Short.IIb.TailSourceAndGlobalEnergy)
    (hLS : UnforcedLeray.Short.IIb.LocalSmoothing) :
    UnforcedLeray.Short.IIb.FlatReconstruction :=
  flatReconstruction_of_leaves
    flatFreeInteractionStep_proof
    flatColumnHpStep_proof
    flatReconstructionIdentityStep_proof
    hGE hLS

end UnforcedLeray.Short.IIb
