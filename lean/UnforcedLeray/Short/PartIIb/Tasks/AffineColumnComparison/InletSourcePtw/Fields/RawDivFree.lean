import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_3
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff.RawContDiff

/-!


Source `the November 2 reference manuscript`
lines 2355-2383, 1214-ff.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem rawDivFree : UnforcedLeray.Short.IIb.RawDivFree :=
  rawDivFree_of rawContDiff

end UnforcedLeray.Short.IIb
