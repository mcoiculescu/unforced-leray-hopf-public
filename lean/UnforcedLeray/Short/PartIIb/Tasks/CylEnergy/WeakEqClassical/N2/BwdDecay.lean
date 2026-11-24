import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_2
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedDeriv

/-!


Source: `the November 2 reference manuscript` lines 2100-2105.

Assembles the two leaves `bwdWeightedSup` and `bwdWeightedDeriv` through `bwdDecay_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bwdDecay : UnforcedLeray.Short.IIb.BwdDecay :=
  bwdDecay_of bwdWeightedSup bwdWeightedDeriv

end UnforcedLeray.Short.IIb
