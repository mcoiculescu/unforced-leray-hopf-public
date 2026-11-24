import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.Spatial
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay.WeightedSup.MaxPrinciple.ExistsMax

/-!
# `BwdMaxPrinciple` (SP 2100-2105): weak maximum principle on the periodic strip.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem bwdMaxPrinciple : UnforcedLeray.Short.IIb.BwdMaxPrinciple :=
  bwdMaxPrinciple_of mpExistsMax mpSpatial

end UnforcedLeray.Short.IIb
