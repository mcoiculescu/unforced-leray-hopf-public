import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3.Moment
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3.Majorant
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1_2_3.Bounded

/-!
# `T0adjFormulaDom` (task `PartIII-b:C/flatset/col/7/3/2/1/2/3`, assembly)

Source `the November 2 reference manuscript` 1650-1656.  The domination follows from
the planar heat moment bound (`plane_heat_moment`), the `L²(H)` majorant (`mem_lp_majorant`) and the
boundedness of smooth band tests (`merid_test_bounded`), through `t0adj_formula_dom_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **`T0adjFormulaDom`** (source 1650-1656): near every `t > 0` the formula applied to `A₀*ζ` is
dominated by one `L²(H)` function, uniformly in the age. -/
theorem t0adj_formula_dom : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0adjFormulaDom :=
  t0adj_formula_dom_of plane_heat_moment mem_lp_majorant merid_test_bounded

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
