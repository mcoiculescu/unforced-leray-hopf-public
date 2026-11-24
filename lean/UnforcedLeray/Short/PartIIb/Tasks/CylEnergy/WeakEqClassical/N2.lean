import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdExists
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N2.BwdDecay

/-!
# Part II-b, task `PartII-b:T22/2/3` (`CylBackwardSolve`): assembly

The statement follows from `cylBackwardSolve_of` applied to the two leaves `bwdExists` and `bwdDecay`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cylBackwardSolve : UnforcedLeray.Short.IIb.CylBackwardSolve :=
  cylBackwardSolve_of bwdExists bwdDecay

end UnforcedLeray.Short.IIb

end
