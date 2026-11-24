import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradBound

/-!
# `PartII-b:T10/7` (`GradRecovery`): assembly of `GradWeak` and `GradBound`

Source of record: `the November 2 reference manuscript`, lines 1912-1921
and 1639-1668. Combines `gradWeak_proof` (`PartII-b:T10/7/1`) and `gradBound_proof`
(`PartII-b:T10/7/2`) via `gradRecovery_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem gradRecovery_proof : UnforcedLeray.Short.IIb.GradRecovery :=
  gradRecovery_of gradWeak_proof gradBound_proof

end UnforcedLeray.Short.IIb

end
