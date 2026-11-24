import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Dominate.TailSmooth
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Dominate.TailD
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.Cont
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.GaussInt

/-!
# Part II-b, task `PartII-b:T12/7/5/3` (`DeqPdDominate`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The statement is discharged by `deqPdDominate_of` (`Sub/PartIIb_T12_7_5_3.lean`) from the leaves
`deqhpCont`, `deqhpGaussInt`, `deqpdTailSmooth` and `deqpdTailD`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem deqPdDominate : UnforcedLeray.Short.IIb.DeqPdDominate :=
  deqPdDominate_of deqhpCont deqhpGaussInt deqpdTailSmooth deqpdTailD

end UnforcedLeray.Short.IIb
