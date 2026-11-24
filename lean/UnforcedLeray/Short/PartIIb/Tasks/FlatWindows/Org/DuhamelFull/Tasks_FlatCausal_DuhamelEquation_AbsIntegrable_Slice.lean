import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable.Slice
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_7_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Reduction
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Slice_Support

/-!
# Helper for `PartII-b:T12/7/7/2` (`dfe_deqAbsSlice`): the conditional reduction, unconditioned

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

`dfe_deqAbsSlice_of` reduces `dfe_DeqAbsSlice` to `BoxSlice` (leaf `PartII-b:T12/6/2/5`, proved in
`DuhamelSolenoidal/DuhamelIntegrable/BoxSlice.lean`) and `dfe_DeqAbsSupport` (leaf `PartII-b:T12/7/7/2/1`,
proved in `Slice/Support.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/7/2`**: `dfe_DeqAbsSlice`, from the box slice bound and the transpose-test
support bound. -/
theorem dfe_deqAbsSlice : UnforcedLeray.Short.IIb.dfe_DeqAbsSlice :=
  dfe_deqAbsSlice_of boxSlice dfe_deqAbsSupport

end UnforcedLeray.Short.IIb
