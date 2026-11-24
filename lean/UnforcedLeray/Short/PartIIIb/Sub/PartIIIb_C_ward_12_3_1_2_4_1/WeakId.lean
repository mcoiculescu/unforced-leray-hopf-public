import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1_1
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt

/-!


Source of record: `the November 2 reference manuscript`, lines 2042-2046,
1196-1338.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb

/-- Unconditional proof of `RawResidualWeakIdentity`, combining `rawResidualWeakIdentity_of_lift`,
`ringLiftSmoothExt_of`, and `ringAxisSmooth`. -/
theorem rawResidualWeakIdentity_thm : UnforcedLeray.Short.IIb.RawResidualWeakIdentity :=
  rawResidualWeakIdentity_of_lift
    (UnforcedLeray.Short.IIb.ringLiftSmoothExt_of UnforcedLeray.Short.PartIIa.ringAxisSmooth)

end UnforcedLeray.Short.PartIIIb
