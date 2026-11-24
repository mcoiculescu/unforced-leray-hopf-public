import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.WeakId
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1.DerivY

/-!
# `rawDerivRes` (`PartIII-b:C/ward/12/3/1/2/4/1`)

Source of record: `the November 2 reference manuscript`,
lines 2542-2551, 2042-2046, and 1206-1222.

Combines `rawDerivRes_of` with `rawResidualWeakIdentity_thm` (`WeakId.lean`) and
`rawResidualDerivY_thm` (`DerivY.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb

namespace Concrete

/-- Derivative of the raw residual lies in `Y_{q₀}` (`RawDerivRes`). -/
theorem rawDerivRes : RawDerivRes :=
  rawDerivRes_of rawResidualWeakIdentity_thm rawResidualDerivY_thm

end Concrete

export Concrete (rawDerivRes)

end UnforcedLeray.Short.PartIIIb
