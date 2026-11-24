import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFluxLemmas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvZetaStream
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvErrFlat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvSplit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvForcedAdd
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6.VtvFlux.VtvErrTail

/-!
# Part III-b, task `PartIII-b:C/flatset/col/6/5`: the flux cutoff `VtvFlux`

Target (`PartIII-b_C_flatset_col_6.lean`): `VtvFlux`. Source of record:
`the November 2 reference manuscript`, lines 3511-3514.

The proof is the assembly `vtvFlux_of` (`VtvFluxLemmas.lean`) applied to the five proved
ingredients `vtvZetaStream`, `vtvErrFlat`, `vtvSplit`, `vtvForcedAdd`, `vtvErrTail`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Target: `VtvFlux`. The flux cutoff, assembled from the five ingredients. -/
theorem vtvFlux : VtvFlux :=
  vtvFlux_of vtvZetaStream vtvErrFlat vtvSplit vtvForcedAdd vtvErrTail

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
