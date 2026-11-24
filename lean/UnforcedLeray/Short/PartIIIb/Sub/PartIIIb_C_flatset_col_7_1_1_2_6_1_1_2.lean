import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2.R0Invariant

/-!
# `FlatResSol` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/2`)

Source `the November 2 reference manuscript`
1650-1656. The flat resolvent condition follows from the reduction `flatResSol_of` (in `Defs`)
applied to the solenoidal invariance `r0SolenoidalInvariant` (in `R0Invariant`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatResSol : FlatResSol :=
  flatResSol_of r0SolenoidalInvariant

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
