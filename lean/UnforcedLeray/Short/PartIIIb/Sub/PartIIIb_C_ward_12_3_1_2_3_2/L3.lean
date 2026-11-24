import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2_3.L4

/-!
# `PartIII-b:C/ward/12/3/1/2/3/2/3/1`: `MollDerivIdentity` from its three ingredients

Source of record: `the November 2 reference manuscript`, lines 1415-1424
(differentiation of the spatial mollification in the phase slice) and line 2531.

The assembly is `mollDerivIdentity_of` (pointwise reduction) applied to
`mollDerivAtPoint_of` (testing with `PeriodicFundamental`, `MollSliceLocInt`, `MollSliceTest`),
together with the slice facts `mollSliceFacts`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem mollDerivIdentity : MollDerivIdentity :=
  mollDerivIdentity_of mollSliceFacts
    (mollDerivAtPoint_of periodicFundamental mollSliceLocInt mollSliceTest)

end UnforcedLeray.Short.PartIIIb.Concrete
