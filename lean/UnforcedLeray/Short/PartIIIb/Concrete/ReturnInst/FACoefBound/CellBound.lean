import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_9_3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellSumPointwise
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellUnfold
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellGauss

/-!
# `PartIII-b:C/inst/9/3`: `FAcCellBound` from the three Gaussian leaves

Source `the November 2 reference manuscript`
5063-5079 (Gaussian cell norm of `f_A`), 4963-4979 (the fields `V_j`).

Assembles `fAcCellBound_of` (in `Sub/PartIII-b_C_inst_9_3.lean`) with the leaves
`fAcSumPointwise` (`Leaves/CellSumPointwise.lean`), `fAcCellUnfold` (`Leaves/CellUnfold.lean`)
and `fAcGaussInt` (`Leaves/CellGauss.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fAcCellBound : FAcCellBound :=
  fAcCellBound_of fAcSumPointwise fAcCellUnfold fAcGaussInt

end UnforcedLeray.Short.PartIIIb.Concrete
