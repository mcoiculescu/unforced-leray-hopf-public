import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.AbsIntegrable
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Meas
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Reduction
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_AbsIntegrable_Slice

/-!
# Part II-b, task `PartII-b:T12/7/7` (`dfe_deqAbsIntegrable`): joint absolute integrability

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

Assembly of the three leaves `dfe_deqAbsMeas`, `dfe_deqAbsSlice` and `deqAbsTime` through the conditional
reduction `dfe_deqAbsIntegrable_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/7`**: `dfe_DeqAbsIntegrable`, from the measurability, slice and time leaves. -/
theorem dfe_deqAbsIntegrable : UnforcedLeray.Short.IIb.dfe_DeqAbsIntegrable :=
  dfe_deqAbsIntegrable_of dfe_deqAbsMeas dfe_deqAbsSlice deqAbsTime

end UnforcedLeray.Short.IIb
