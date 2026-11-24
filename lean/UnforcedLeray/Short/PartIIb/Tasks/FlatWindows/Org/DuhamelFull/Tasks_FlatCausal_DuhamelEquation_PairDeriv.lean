import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Cont
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Dominate
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Pointwise

/-!
# Part II-b, task `PartII-b:T12/7/5` (`dfe_DeqPairDeriv`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Combines the three leaves `dfe_deqPdPointwise`, `dfe_deqPdCont`, `dfe_deqPdDominate` through
`dfe_deqPairDeriv_of` (`Sub/T12_7_5.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem dfe_deqPairDeriv : UnforcedLeray.Short.IIb.dfe_DeqPairDeriv :=
  UnforcedLeray.Short.IIb.dfe_deqPairDeriv_of UnforcedLeray.Short.IIb.dfe_deqPdPointwise
    UnforcedLeray.Short.IIb.dfe_deqPdCont UnforcedLeray.Short.IIb.dfe_deqPdDominate

end UnforcedLeray.Short.IIb
