import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5.IbpQ
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_5.IbpEta

/-!
# `PlaneGaussDtLap` (task `PartIII-b:C/flatset/col/7/3/2/1/2/5`, assembly)

Source `the November 2 reference manuscript` 1650-1656.  The two coordinate
integration-by-parts facts `PlaneGaussIbpQ` (`plane_gauss_ibp_q`) and `PlaneGaussIbpEta`
(`plane_gauss_ibp_eta`) give `PlaneGaussDtLap` through `plane_gaussDt_lap_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **`PlaneGaussDtLap`** (source 1650-1656): the heat equation for the planar Gaussian kernel. -/
theorem plane_gaussDt_lap : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.PlaneGaussDtLap :=
  plane_gaussDt_lap_of plane_gauss_ibp_q plane_gauss_ibp_eta

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
