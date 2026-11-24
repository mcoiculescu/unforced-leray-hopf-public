import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2.FrechetLscBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2.VtvPSub
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_2.VtvPLsc

/-!
# `PartIII-b:C/flatset/col/6/3/4/2/2/6` (`vtvFubiniOpBound`): assembly

Source of record: `the November 2 reference manuscript`
(around line 4610: integrated Duhamel identity `Y(s,φ) = ∫₀^s R(r,φ) dr`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Operator bound** (source ~4610): the statement `VtvFubiniOpBound`, obtained from
`frechetLscBound`, `vtvPSub` and `vtvPLsc`. -/
theorem vtvFubiniOpBound : VtvFubiniOpBound :=
  vtvFubiniOpBound_of frechetLscBound vtvPSub vtvPLsc

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
