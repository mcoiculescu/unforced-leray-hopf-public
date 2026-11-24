import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Pointwise
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.WeightedInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.DualConstancy.TestZero.RemainderLimit.Measurable

/-!
# Part II-b, leaf `PartII-b:T11/2/2/4` (`DualRemainderLimit`): assembly.

Source: `the November 2 reference manuscript` lines 1923-1927.
The three leaves `dualRemPointwise`, `dualGWeightedInt`, `dualRemMeasurable` feed
`dualRemainderLimit_of`.
-/

set_option autoImplicit false

noncomputable section

theorem DualRemainderLimit_proof : UnforcedLeray.Short.IIb.DualRemainderLimit :=
  UnforcedLeray.Short.IIb.dualRemainderLimit_of
    UnforcedLeray.Short.IIb.dualRemPointwise
    UnforcedLeray.Short.IIb.dualGWeightedInt
    UnforcedLeray.Short.IIb.dualRemMeasurable
