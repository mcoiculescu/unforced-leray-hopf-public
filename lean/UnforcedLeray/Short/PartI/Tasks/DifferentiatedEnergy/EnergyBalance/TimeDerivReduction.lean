import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2
import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_2.Instance

/-!
# Part I, task `PartI:T08/4/1/2` (`TrainJetEnergyTimeDerivOfLocal`): proof

Source `the November 2 reference manuscript` lines 341-348.
Composes the reduction `trainJetEnergyTimeDerivOfLocal_of` with the scalar leaf
`trainWordEnergyHasDerivAt_proof` (task `PartI:T08/4/1/2/2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainJetEnergyTimeDerivOfLocal_proof :
    UnforcedLeray.Short.PartI.TrainJetEnergyTimeDerivOfLocal :=
  UnforcedLeray.Short.PartI.trainJetEnergyTimeDerivOfLocal_of
    UnforcedLeray.Short.PartI.trainWordEnergyHasDerivAt_proof

end UnforcedLeray.Short.PartI
