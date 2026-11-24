import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4_1_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.Exists
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.Membership
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.Approx
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.SliceId
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.Select.Mollify.WeakD

/-!
# `selMollify`: the mollification step of `sliceSelect`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
Assembly: the five analytic facts `mollExists`, `convYMembership`, `convYApprox`, `convYSliceId`,
`convYWeakD` (each in its own module under `Select/Mollify/`) are fed to `selMollify_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem selMollify : SelMollify :=
  selMollify_of mollExists convYMembership convYApprox convYSliceId convYWeakD

end UnforcedLeray.Short.PartIIIb.Concrete
