import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L4

/-!
# `PartIII-b:C/rep/8/3/2/1`: `GaussSumEA` from the four lattice-sum leaves

Source `the November 2 reference manuscript` 4963-4985, 4978.
`gaussSumEA_of` (in `Sub/PartIII-b_C_rep_8_3_2_1.lean`) reduces `GaussSumEA` to
`GaussSumSmooth`, `GaussSumV`, `GaussSumHess`, `GaussSumGrad`, which are proved in the leaves
`L1`..`L4`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`e_A` is the affine expression of the summed Gaussians** (source 4963-4985), assembled
from the four lattice-sum leaves. -/
theorem gaussSumEA : GaussSumEA :=
  gaussSumEA_of gaussSumSmooth gaussSumV gaussSumHess gaussSumGrad

end UnforcedLeray.Short.PartIIIb.Concrete

end
