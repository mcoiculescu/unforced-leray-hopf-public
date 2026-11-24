import UnforcedLeray.Short.PartI.Sub.PartI_T09_5
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1.Reduction
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1.VcCont
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.FiniteEnergyClass

/-!
# Part I, task `PartI:T09/5/org/1`: right-continuity of the jet energies of the train error

Source of record: `the November 2 reference manuscript`, lines 270-288 (BUC class and
finite-energy mild solution), 294 (`V_c^p`), 341-344.

Proof: `trainJetEnergyRightCont_proof_of` reduces `TrainJetEnergyRightCont` to `TrainJetEnergyToZero`;
`trainJetEnergyToZero_of_cont` (Reduction) proves the latter from `VcCellL2Cont` (VcCont) and
`TrainFiniteEnergyClass` (FiniteEnergyClass), which are both proved in their files.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- **Target.** Every jet energy of the comparison error `v - V_c^p` is right-continuous at age `0`
for every BUC train (lines 270-288, 294, 341-344). -/
theorem trainJetEnergyRightCont_proof : TrainJetEnergyRightCont :=
  trainJetEnergyRightCont_proof_of
    (trainJetEnergyToZero_of_cont vcCellL2Cont_proof trainFiniteEnergyClass_proof)

end UnforcedLeray.Short.PartI
