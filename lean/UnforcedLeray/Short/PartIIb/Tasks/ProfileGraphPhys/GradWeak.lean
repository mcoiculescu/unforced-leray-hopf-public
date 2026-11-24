import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.LiftRead
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.OfLift

/-!
# `PartII-b:T10/7/1` (`GradWeak`): assembly of the two proved leaves

Source of record: `the November 2 reference manuscript` lines 1912-1921, 1639-1668.
Combines `gradLiftRead` (`PartII-b:T10/7/1/1`) and `gradWeakOfLift` (`PartII-b:T10/7/1/2`)
via `gradWeak_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem gradWeak_proof : UnforcedLeray.Short.IIb.GradWeak := by
  exact gradWeak_of gradLiftRead gradWeakOfLift

end UnforcedLeray.Short.IIb

end
