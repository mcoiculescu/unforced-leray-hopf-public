import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Cauchy
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Complete
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Limit

/-!
# `sliceSelect`: assembly

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
The four analytic steps (mollification, Cauchy property, completeness, limit identification) are
proved in `Slice/Select/{Mollify,Cauchy,Complete,Limit}.lean`; this file composes them via
`sliceSelect_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Measurable periodic selection of the slice derivatives in `Y_2` (source 1351-1362, 1470-1480). -/
theorem sliceSelect : SliceSelect :=
  sliceSelect_of selMollify selCauchy selComplete selLimit

end UnforcedLeray.Short.PartIIIb.Concrete
