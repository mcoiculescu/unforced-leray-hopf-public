import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_3
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcSumPointwise
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellUnfold
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellGauss

/-!
# `PartIII-b:C/inst/10/3`: `EAcCellBound` from the Gaussian leaves

Source `the November 2 reference manuscript` 4963-4975 (`V_j`, `p_j`), 4971-4972
(`e_A`), 5063-5079 (cell norms).  The bound is `eAcCellBound_of` (`Sub/PartIII-b_C_inst_10_3.lean`)
applied to the leaves `eAcSumPointwise`, `fAcCellUnfold`, `fAcGaussInt`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eaCCellBound : EAcCellBound :=
  eAcCellBound_of eAcSumPointwise fAcCellUnfold fAcGaussInt

end UnforcedLeray.Short.PartIIIb.Concrete
