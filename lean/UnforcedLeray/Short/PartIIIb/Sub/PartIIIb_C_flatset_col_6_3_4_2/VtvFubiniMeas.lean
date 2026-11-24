import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_1.VtvFlowRep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_1.VtvKfMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_4_2_1.VtvKflowMeas

/-!
# `PartIII-b:C/flatset/col/6/3/4/2/1` (`vtvFubiniMeas`): joint measurability

Source of record: `the November 2 reference manuscript` (line 4610, the integrated
Duhamel identity `Y(s,φ) = ∫₀^s R(r,φ) dr`). The statement is discharged by the assembly lemma
`vtvFubiniMeas_of` of the decomposition module, from the three leaves `vtvFlowRep`, `vtvKfMeas`
and `vtvKflowMeas`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Joint measurability** (source 4610): the integrated Duhamel kernel is a.e. jointly
measurable in `((s,r),x)`, by `vtvFubiniMeas_of vtvFlowRep vtvKfMeas vtvKflowMeas`. -/
theorem vtvFubiniMeas : VtvFubiniMeas :=
  vtvFubiniMeas_of vtvFlowRep vtvKfMeas vtvKflowMeas

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
