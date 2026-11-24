import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_HeatPair_Cont
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_HeatPair_Tail
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_HeatPair_Unif

/-!
# Part II-b, task `PartII-b:T12/7/4` (`dfe_DeqHeatPair`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The four leaves `dfe_deqhpCont`, `dfe_deqhpUnif`, `dfe_deqhpTail`, `deqhpGaussInt` feed `dfe_deqHeatPair_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem dfe_deqHeatPair : UnforcedLeray.Short.IIb.dfe_DeqHeatPair :=
  dfe_deqHeatPair_of dfe_deqhpCont dfe_deqhpUnif dfe_deqhpTail deqhpGaussInt

end UnforcedLeray.Short.IIb
