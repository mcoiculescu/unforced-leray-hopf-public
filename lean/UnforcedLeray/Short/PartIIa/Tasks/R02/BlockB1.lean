import UnforcedLeray.Short.PartIIa.Sub.R02
import UnforcedLeray.Short.PartIIa.Calc.BlockB1
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.CoeffB1Eq
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.CoeffB1EtaEq
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.CoeffB1ShiftEq
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.CoeffB1QEq
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.HeatJetEigen
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.JetLinear
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.TrainPartsSmooth
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.FluctJetUnif
import UnforcedLeray.Short.PartIIa.Calc.BlockB1.RemJetUnif

/-!
# Part II-a, task `PartII-a:R02/9`: the `B₁` block of the late table (assembly)

No new mathematics: the block follows from `BlockB1.ringLateB1_of_parts` (`Calc/BlockB1.lean`)
and its nine leaves (`Calc/BlockB1/*.lean`).  Source of record:
`the November 2 reference manuscript`, lines 1243-1276.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R02/9`**: the `B₁` block of the late residual table, from the late ingredients. -/
theorem ringLateB1_of (h : LateIngredients) : RingLateB1 :=
  BlockB1.ringLateB1_of_parts h BlockB1.coeffB1Eq BlockB1.coeffB1EtaEq BlockB1.coeffB1ShiftEq
    BlockB1.coeffB1QEq BlockB1.heatJetEigen BlockB1.jetLinear
    (BlockB1.trainPartsSmooth_of h.smooth) (BlockB1.fluctJetUnif_of h.fluct)
    (BlockB1.remJetUnif_of h.remainder)

end UnforcedLeray.Short.PartIIa
