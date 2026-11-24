import UnforcedLeray.Short.PartIIb.Sub.T12_7_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.Cont
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.Unif
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.Tail
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.HeatPair.GaussInt

/-!
# Part II-b, task `PartII-b:T12/7/4` (`DeqHeatPair`): assembly

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
The four leaves `deqhpCont`, `deqhpUnif`, `deqhpTail`, `deqhpGaussInt` feed `deqHeatPair_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem deqHeatPair : UnforcedLeray.Short.IIb.DeqHeatPair :=
  deqHeatPair_of deqhpCont deqhpUnif deqhpTail deqhpGaussInt

end UnforcedLeray.Short.IIb
