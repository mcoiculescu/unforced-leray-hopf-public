import UnforcedLeray.Short.PartI.Sub.PartI_T08_4
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDeriv
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.PairSplit

/-!
# Part I, task `PartI:T08/4` (`TrainJetEnergyBalance`): proof

Source `the November 2 reference manuscript` lines 341-348 and the error equation
326-329. Composes the decomposition `trainJetEnergyBalance_of` with the two leaf proofs
`trainJetEnergyTimeDeriv_proof` (task `PartI:T08/4/1`) and `trainJetPairSplit_proof`
(task `PartI:T08/4/2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainJetEnergyBalance_proof : UnforcedLeray.Short.PartI.TrainJetEnergyBalance :=
  UnforcedLeray.Short.PartI.trainJetEnergyBalance_of
    UnforcedLeray.Short.PartI.trainJetEnergyTimeDeriv_proof
    UnforcedLeray.Short.PartI.trainJetPairSplit_proof

end UnforcedLeray.Short.PartI
