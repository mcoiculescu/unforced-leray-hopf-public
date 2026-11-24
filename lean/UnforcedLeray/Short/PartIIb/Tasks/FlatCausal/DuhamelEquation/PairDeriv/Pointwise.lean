import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_7_5_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Pointwise.JointDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Pointwise.CptLap
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Pointwise.SmoothDEq

/-!
# Part II-b, task `PartII-b:T12/7/5/1` (`DeqPdPointwise`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
Combines the three lemmas `deqpdJointDeriv`, `deqpdCptLap`, `deqpdSmoothDEq` through
`deqPdPointwise_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem deqPdPointwise : UnforcedLeray.Short.IIb.DeqPdPointwise :=
  UnforcedLeray.Short.IIb.deqPdPointwise_of UnforcedLeray.Short.IIb.deqpdJointDeriv
    (UnforcedLeray.Short.IIb.deqpdSmoothDEq UnforcedLeray.Short.IIb.deqpdCptLap)

end UnforcedLeray.Short.IIb
