import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.Lemma1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.Lemma2

/-!
# `SFCDatumReg` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1`)

Source `the November 2 reference manuscript`
lines 1650-1656, 1684-1689, 3426-3430. The regular datum follows from the two
analytic lemmas `flatProjSmoothRegular_holds` (Lemma1) and `planeHeatAeDatum_holds`
(Lemma2) through `sfcDatumReg_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `SFCDatumReg` holds: `sfcDatumReg_of` applied to the flat-projection regularity and the
a.e.-class invariance of the plane heat. -/
theorem sfcDatumReg : SFCDatumReg :=
  sfcDatumReg_of flatProjSmoothRegular_holds planeHeatAeDatum_holds

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
