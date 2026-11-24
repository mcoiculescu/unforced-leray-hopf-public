import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivRepAE
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivPt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivDom
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_2_1.AdjDerivLp

/-!
# `t0adj_strong_deriv`: the strong `L²(H)` derivative of `T₀(s)*` (organizer task
`PartIII-b:C/flatset/col/7/3/2/1/2/org`, source `the November 2 reference manuscript`
1650-1656, viscosity `ν > 0`).

Assembled from the five source facts: representatives (`t0adj_rep_ae`), pointwise time derivative
(`t0adj_pt_deriv`), `L²(H)` domination (`t0adj_formula_dom`), and the abstract `L²` derivative lemma
(`lp_hasDerivAt_of_pointwise`), through the reduction `t0adjStrongDerivPos_of` of `AdjDerivOf.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem t0adj_strong_deriv : UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.T0adjStrongDerivPos :=
  t0adjStrongDerivPos_of t0adj_rep_ae t0adj_pt_deriv t0adj_formula_dom lp_hasDerivAt_of_pointwise

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
