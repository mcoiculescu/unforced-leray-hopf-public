import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Dominate
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_PartIIb_T12_7_5_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_T12_7_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_HeatPair_Cont
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Dominate_TailD
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Tasks_FlatCausal_DuhamelEquation_PairDeriv_Dominate_TailSmooth

/-!
# Part II-b, task `PartII-b:T12/7/5/3` (`dfe_DeqPdDominate`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The statement is discharged by `dfe_deqPdDominate_of` (`Sub/PartIIb_T12_7_5_3.lean`) from the leaves
`dfe_deqhpCont`, `deqhpGaussInt`, `dfe_deqpdTailSmooth` and `dfe_deqpdTailD`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem dfe_deqPdDominate : UnforcedLeray.Short.IIb.dfe_DeqPdDominate :=
  dfe_deqPdDominate_of dfe_deqhpCont deqhpGaussInt dfe_deqpdTailSmooth dfe_deqpdTailD

end UnforcedLeray.Short.IIb
