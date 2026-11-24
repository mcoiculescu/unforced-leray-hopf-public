import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Pointwise
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_PartIIb_T12_7_5_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Pointwise_CptLap
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Pointwise_JointDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Pointwise_SmoothDEq

/-!
# Part II-b, task `PartII-b:T12/7/5/1` (`dfe_DeqPdPointwise`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Combines the three lemmas `dfe_deqpdJointDeriv`, `dfe_deqpdCptLap`, `dfe_deqpdSmoothDEq` through
`dfe_deqPdPointwise_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dfe_deqPdPointwise : UnforcedLeray.Short.IIb.dfe_DeqPdPointwise :=
  UnforcedLeray.Short.IIb.dfe_deqPdPointwise_of UnforcedLeray.Short.IIb.dfe_deqpdJointDeriv
    (UnforcedLeray.Short.IIb.dfe_deqpdSmoothDEq UnforcedLeray.Short.IIb.dfe_deqpdCptLap)

end UnforcedLeray.Short.IIb
