import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.CplxLift
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.R0Transpose
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.ZetaPhiTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.ZetaPhiSolenoidal
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairIntegrable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.WeakPairValue

/-!
# `bodyColumnWeak` (organizer task `PartIII-b:C/flatset/col/7/3/org`)

Composition of the six source facts with `bodyColumnWeak_of` (in `Of.lean`).
Source of record `the November 2 reference manuscript`: 1650-1656, 1684-1689.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem bodyColumnWeak : BodyColumnWeak :=
  bodyColumnWeak_of cplxLift r0TransposeIdentity zetaPhiMeridTest zetaPhiSolenoidal
    weakPairIntegrable weakPairValue

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
