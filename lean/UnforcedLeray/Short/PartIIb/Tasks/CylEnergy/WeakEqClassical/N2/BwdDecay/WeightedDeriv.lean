import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.DriftC2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Grad
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv.Lap

/-!
# `BwdWeightedDeriv` (SP 2085-2105): weighted bounds for the first and second derivatives.

Assembles the three leaves `bwdDriftC2Bound`, `bwdWeightedGrad`, `bwdWeightedLap` through
`bwdWeightedDeriv_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bwdWeightedDeriv : UnforcedLeray.Short.IIb.BwdWeightedDeriv :=
  bwdWeightedDeriv_of bwdDriftC2Bound bwdWeightedGrad bwdWeightedLap

end UnforcedLeray.Short.IIb
