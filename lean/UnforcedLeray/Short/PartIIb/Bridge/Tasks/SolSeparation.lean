import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:T10/org/2`: solenoidal tests separate `Y_{q,σ}`.** Assembly of the three
unconditional inputs (slice solenoidality, slice orthogonality, spatial nondegeneracy) through
`solSeparation_of` (SP 1409-1412, 1498-1500). -/
theorem solSeparation : SolSeparation :=
  solSeparation_of solSepSliceSol solSepSliceOrth solSepSpatial

end UnforcedLeray.Short.IIb
