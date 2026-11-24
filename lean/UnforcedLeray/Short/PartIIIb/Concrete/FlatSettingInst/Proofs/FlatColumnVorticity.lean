import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvDuhamelDatum
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvMellin
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvGInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvXiInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_5.FcvFubini
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.FlatXiRegular

/-!
# `FlatColumnVorticity` (task `PartIII-b:C/flatset/col/5`)

Source of record `the November 2 reference manuscript`: 4610, 4464-4467, 2819-2836,
4614-4615.  Assembly of `flatColumnVorticity_of` (`Sub/PartIII-b_C_flatset_col_5.lean`) with the five
leaves `fcvDuhamelDatum`, `fcvMellin`, `fcvGInt`, `fcvXiInt flatXiRegular`, `fcvFubini flatXiRegular`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatColumnVorticity : FlatColumnVorticity :=
  flatColumnVorticity_of fcvDuhamelDatum fcvMellin fcvGInt (fcvXiInt flatXiRegular)
    (fcvFubini flatXiRegular)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
