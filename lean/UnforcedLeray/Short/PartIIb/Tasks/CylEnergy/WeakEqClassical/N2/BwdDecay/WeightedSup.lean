import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_1
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.DriftBound
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.Barrier
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple

/-!
# `BwdWeightedSup` (SP 2100-2105): weighted maximum principle for the backward problem.

Assembles the three leaves `bwdDriftBound`, `bwdBarrier`, `bwdMaxPrinciple` through
`bwdWeightedSup_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bwdWeightedSup : UnforcedLeray.Short.IIb.BwdWeightedSup :=
  bwdWeightedSup_of bwdDriftBound bwdBarrier bwdMaxPrinciple

end UnforcedLeray.Short.IIb
