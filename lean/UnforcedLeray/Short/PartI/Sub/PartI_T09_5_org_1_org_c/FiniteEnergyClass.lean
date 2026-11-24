import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.JetSumLimsup
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.Pointwise
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.DatumL2
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.ScheffeFamily

/-!
# `PartI:T09/5/org/1/org/c`: the finite-energy class of trains (assembly)

Source of record: `the November 2 reference manuscript`, lines 270-288.
The four Props of `trainFiniteEnergyClass_of` are supplied by the proved lemma files.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem trainFiniteEnergyClass_proof : TrainFiniteEnergyClass :=
  trainFiniteEnergyClass_of trainJetSumLimsup_proof trainJetPointwiseAt0_proof
    trainDatumJetL2Finite_proof scheffeL2FamilyAt0_proof

end UnforcedLeray.Short.PartI
