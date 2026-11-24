import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvStreamFlat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvSlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvTime
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFubini
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux

/-!
# `PartIII-b:C/flatset/col/6`: `VorticityToVelocity`

Source of record: `the November 2 reference manuscript` (73 pages), lines
3420-3426, 3511-3514, 4610-4612 (decomposition of `VorticityToVelocity`).

Assembly: the compiled reduction `vorticityToVelocity_of` (Sub module `PartIII-b_C_flatset_col_6`)
applied to the five step lemmas `vtvStreamFlat`, `vtvSlice`, `vtvTime`, `vtvFubini`, `vtvFlux`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vorticityToVelocity : VorticityToVelocity :=
  vorticityToVelocity_of vtvStreamFlat vtvSlice vtvTime vtvFubini vtvFlux

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
