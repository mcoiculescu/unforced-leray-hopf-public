import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Calc.BlockB3
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.CoeffB3Eq
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.CoeffB3EtaEq
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.CoeffB3ShiftEq
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.CoeffB3QEq
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.HeatJetEigen
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.JetLinear
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.TrainPartsSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.FluctJetUnif3
import UnforcedLeray.Short.PartIIa.Tasks.R02.BlockB3.RemJetUnif3

/-!
# Part II-a, task `PartII-a:R02/11`: the `B₃` block of the late table (assembly)

No new mathematics: the block follows from `BlockB3.ringLateB3_of_parts` (`Calc/BlockB3.lean`)
and its nine leaves (`Tasks/R02/BlockB3/*.lean`).  Source of record:
`the November 2 reference manuscript`, lines 1243-1276.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/11`**: the `B₃` block of the late residual table, from the late ingredients. -/
theorem ringLateB3_of (h : LateIngredients) : RingLateB3 :=
  BlockB3.ringLateB3_of_parts h BlockB3.coeffB3Eq BlockB3.coeffB3EtaEq BlockB3.coeffB3ShiftEq
    BlockB3.coeffB3QEq BlockB3.heatJetEigen BlockB3.jetLinear
    (BlockB3.trainPartsSmooth_of h.smooth) (BlockB3.fluctJetUnif3_of h.fluct)
    (BlockB3.remJetUnif3_of h.remainder)

end UnforcedLeray.Short.PartIIa
