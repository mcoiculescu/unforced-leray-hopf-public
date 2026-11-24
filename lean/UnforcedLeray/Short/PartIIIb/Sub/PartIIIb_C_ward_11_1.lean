import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_3

/-!
# `PartIII-b:C/ward/11/1`: `WardXYoungL2`

Source of record: `the November 2 reference manuscript` (73 pages), 4194-4196,
3633-3648, 3696-3697.

Combines the unconditional `wardX0YoungL2_proved` (`ward/10/1`) and `wardStreamCorrYoungL2_proved`
(`ward/10/2`) with `wardXYoungL2_of_parts` (`ward/10/3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`X, DX ∈ Y₂` on the young support** (`PartIII-b:C/ward/11/1`, source 4194-4196). -/
theorem wardXYoungL2_proved : WardXYoungL2 :=
  wardXYoungL2_of_parts wardX0YoungL2_proved wardStreamCorrYoungL2_proved

end UnforcedLeray.Short.PartIIIb.Concrete
end
