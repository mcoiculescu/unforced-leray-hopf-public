import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2.GainLe
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2.FiberNull
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_3_2_2.BoxApprox

/-!
# `PartIII-b:C/rep/5/1/1/3/2/2`: `BinDensityTransfer` from its three ingredients

Assembles `binDensityTransfer_of` (parent file) with `velBinGainLe`, `ageFiberNull` and
`thinBoxApprox`.  Source `the November 2 reference manuscript`
3902-3912.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem binDensityTransfer : BinDensityTransfer :=
  binDensityTransfer_of velBinGainLe ageFiberNull thinBoxApprox

end UnforcedLeray.Short.PartIIIb.Concrete
