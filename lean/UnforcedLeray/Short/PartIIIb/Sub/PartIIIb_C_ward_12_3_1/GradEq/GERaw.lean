import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4.RawDerivRes

/-!
# `GERaw` (assembly, source 2542-2551, 1206-1222)

Task `PartIII-b:C/ward/12/3/1/2/4`. Source of record:
`the November 2 reference manuscript`.

Direct application of `gERaw_of` (in `PartIII-b_C_ward_12_3_1_2_4.lean`) to the accepted leaf
`rawDerivRes` (`PartIII-b_C_ward_12_3_1_2_4/RawDerivRes.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gERaw : GERaw :=
  gERaw_of rawDerivRes

end UnforcedLeray.Short.PartIIIb.Concrete
