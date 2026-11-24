import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_3_2_1.L1.Common

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **PartIII-b:C/rep/8/3/2/1/2.** Summability of the Gaussian velocity lattice sum
(source 4978). -/
theorem gaussSumV : GaussSumV := by
  intro ν s hν hs x
  exact summable_vj_translate hν hs x

end UnforcedLeray.Short.PartIIIb.Concrete
