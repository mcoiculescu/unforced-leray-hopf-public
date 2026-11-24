import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_2.L2ae
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_2.Eq

/-!
# `VtvSlice` (source 3511-3514, 3420-3426, 4610-4612)

Source of record: `the November 2 reference manuscript` (73 pages).

`VtvSlice` is assembled from the a.e.-age `L²` statement `SliceL2ae` (`L2ae.lean`) and the
fixed-age identity `SliceEq` (`Eq.lean`) by `vtvSlice_of` (`Sub/PartIII-b_C_flatset_col_6_2.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **The slice identity** (source 3511-3514, 3420-3426): for a.e. age the tested forced
integrand against `∇^⊥ζ(s)` is integrable on the cell and integrates to `streamSlice`. -/
theorem vtvSlice : VtvSlice := vtvSlice_of sliceL2ae sliceEq

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
