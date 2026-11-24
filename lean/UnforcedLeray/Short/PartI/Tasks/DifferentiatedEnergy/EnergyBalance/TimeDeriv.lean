import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivReduction

/-!
# Part I, task `PartI:T08/4/1` (`TrainJetEnergyTimeDeriv`): proof

Source `the November 2 reference manuscript` lines 341-348.
Composes the decomposition `trainJetEnergyTimeDeriv_proof_of` with the two leaf proofs
`trainTimeDerivLocalL2_proof` (task `PartI:T08/4/1/1`) and
`trainJetEnergyTimeDerivOfLocal_proof` (task `PartI:T08/4/1/2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainJetEnergyTimeDeriv_proof :
    UnforcedLeray.Short.PartI.TrainJetEnergyTimeDeriv :=
  UnforcedLeray.Short.PartI.trainJetEnergyTimeDeriv_proof_of
    UnforcedLeray.Short.PartI.trainTimeDerivLocalL2_proof
    UnforcedLeray.Short.PartI.trainJetEnergyTimeDerivOfLocal_proof

end UnforcedLeray.Short.PartI
