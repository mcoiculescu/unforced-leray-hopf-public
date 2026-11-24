import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.LiftAe
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.CplxMeridTest
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.LerayPartBasic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FinModeProj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.TruncTendsto
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.AeLimitOfLp

/-!
# `FlatProjSmoothRegular` holds (organize task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2/1/1`)

Source of record `the November 2 reference manuscript`
lines 1650-1656, 1676, 1684-1689, 1713-1737. The six lemma Props of `FlatLerayDefs` are proved in the
sibling files (`liftAe`, `cplxMeridTest`, `lerayPartBasic`, `finModeProj`, `truncTendsto`,
`aeLimitOfLp`); this file assembles them through `flatProjSmoothRegular_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Flat Leray regularity of smooth data: the six lemma Props discharge `FlatProjSmoothRegular`
(`FlatLeray.flatProjSmoothRegular_of`). -/
theorem flatProjSmoothRegular_holds : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatProjSmoothRegular :=
  FlatLeray.flatProjSmoothRegular_of FlatLeray.liftAe FlatLeray.cplxMeridTest
    FlatLeray.lerayPartBasic FlatLeray.finModeProj FlatLeray.truncTendsto FlatLeray.aeLimitOfLp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
