import UnforcedLeray.Short.PartIIb.Sub.T12_7_5
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Pointwise
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Cont
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Dominate

/-!
# Part II-b, task `PartII-b:T12/7/5` (`DeqPairDeriv`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Combines the three leaves `deqPdPointwise`, `deqPdCont`, `deqPdDominate` through
`deqPairDeriv_of` (`Sub/T12_7_5.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqPairDeriv : UnforcedLeray.Short.IIb.DeqPairDeriv :=
  UnforcedLeray.Short.IIb.deqPairDeriv_of UnforcedLeray.Short.IIb.deqPdPointwise
    UnforcedLeray.Short.IIb.deqPdCont UnforcedLeray.Short.IIb.deqPdDominate

end UnforcedLeray.Short.IIb
