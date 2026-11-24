import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRotInv
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLBuild

/-!
# `PartII-b:T10/7/1/1` (`GradLiftRead`): assembly of the lift reading

Source of record: `the November 2 reference manuscript` lines 1912-1921.
Composes `gl_rotInv` (`GLRotInv`) and `gl_build` (`GLBuild`) through `gradLiftRead_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem gradLiftRead : UnforcedLeray.Short.IIb.GradLiftRead :=
  gradLiftRead_of gl_rotInv gl_build

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gradLiftRead
