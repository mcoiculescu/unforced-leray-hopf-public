import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_2
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileMeasOfLift
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfilePosPeriodic

/-!
# Part II-b, task `PartII-b:T10/2` (`ProfileRegularize`)

Source of record: `the November 2 reference manuscript`, lines 1902-1906, 1633-1637.
Derived from `profileRegularize_of` (Sub `PartII-b_T10_2`) applied to the leaves
`profileMeasOfLift_proof` (T10/2/1) and `profilePosPeriodic_proof` (T10/2/2).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem profileRegularize_proof : UnforcedLeray.Short.IIb.ProfileRegularize :=
  profileRegularize_of profileMeasOfLift_proof profilePosPeriodic_proof

end UnforcedLeray.Short.IIb

end
