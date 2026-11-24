import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_5
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.StressDivLocal.QcJet

/-!
# Part I, task `PartI:T08/4/1/1/5` (`TrainStressDivLocal`): proof

Source `the November 2 reference manuscript` lines 326-335 and 2217-2234.

`trainStressDivLocal_of` reduces `TrainStressDivLocal` to the leaf `QcJetLocalL2`, and
`qcJetLocalL2_proof` (task `PartI:T08/4/1/1/5/4`) supplies that leaf.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem trainStressDivLocal_proof : UnforcedLeray.Short.PartI.TrainStressDivLocal :=
  trainStressDivLocal_of qcJetLocalL2_proof

end UnforcedLeray.Short.PartI
