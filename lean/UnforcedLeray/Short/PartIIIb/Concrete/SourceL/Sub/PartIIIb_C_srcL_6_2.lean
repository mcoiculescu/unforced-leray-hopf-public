import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_srcL_6_2_3

/-!
# `PartIII-b:C/srcL/6/2`: derivative decay of `Z` (`XSZDecay`)

Source of record: `the November 2 reference manuscript` lines 4776-4791, 4917-4937.
The decomposition `xsZDecay_of` (compiled in `Sub/PartIII-b_C_srcL_6_2.lean`) reduces
`XSZDecay` to the smoothness of the zero-width Young field (`PartIII-b:C/srcL/6/2/2`) and its
derivative decay (`PartIII-b:C/srcL/6/2/3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xsZDecay : XSZDecay := by
  exact xsZDecay_of xsYoungWSmooth xsYoungWDecay

end UnforcedLeray.Short.PartIIIb.Concrete
