import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.LerayPairSol
import UnforcedLeray.Short.PartIIb.Bridge.Tasks.SolSeparation
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ProfileRegularize
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.WeakVecCongr
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.FreeResponseCongr
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ResponseProfile
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.DriftRecovery
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradRecovery

/-!
# Part II-b, task `PartII-b:T10` (`ProfileGraphPhys`): assembly

Source of record: `the November 2 reference manuscript`, lines 1912-1938.
Assembly of `profileGraphPhys_of` (`Sub/PartII-b_T10.lean`) with `lerayPairSol`, `solSeparation`,
and the seven lemma theorems `nvCInYr_proof`, `profileRegularize_proof`, `weakVecCongr_proof`,
`freeResponseCongr_proof`, `responseProfile_proof`, `driftRecovery_proof`, `gradRecovery_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem profileGraphPhys_proof : UnforcedLeray.Short.IIb.ProfileGraphPhys :=
  profileGraphPhys_of lerayPairSol solSeparation nvCInYr_proof profileRegularize_proof
    weakVecCongr_proof freeResponseCongr_proof responseProfile_proof driftRecovery_proof
    gradRecovery_proof

end UnforcedLeray.Short.IIb

end
