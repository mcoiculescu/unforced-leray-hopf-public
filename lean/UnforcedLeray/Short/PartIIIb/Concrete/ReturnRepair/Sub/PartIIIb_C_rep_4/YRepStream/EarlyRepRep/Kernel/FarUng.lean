import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep.Kernel.Ungained
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.FarKernel

/-!
# `PartIII-b:C/rep/4/4/1/org/8/1/org/1`: `farRepRepUng` (re-export)

Source `the November 2 reference manuscript` 5303-5308, 5323-5339, 3902-3920.

The leaf `FarRepRepUng` of `Ungained.lean` is the one leaf of both the late-output entry
(`LateSepKernel`, task `PartIII-b:C/rep/4/4/1/org/6/1`) and the early-source entry
(`EarlyRepRepKernel`, task `PartIII-b:C/rep/4/4/1/org/8/1`). The late tree used to declare its own
copy of the leaf; the copy is removed (organizer item `ORG:clash-pass`), so its proof
`farRepRepUng : FarRepRepUng Pl σ₀ mZ dm dp` in `LateRepRep/SepKernel/FarKernel.lean` (task
`PartIII-b:C/rep/4/4/1/org/6/1/5`, from `sopSubIsFarSeq`, `farVelYoungBox`, `repRecvConv` and
`farRepExtend` by `farRepRepUng_of`) proves the target of this task. It is imported above; this
module declares nothing new.
-/
