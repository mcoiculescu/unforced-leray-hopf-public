import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_7
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_9

/-!
# Pressure Helmholtz identity (`PartIII-b:C/rep/8/2/pres/3/2/1`)

Source of record: `the November 2 reference manuscript`
(73 pages): lines 1213-1225, 4139-4141, 5245-5260, 5272-5281.

Combines the organizer reduction `SeqData.presHelmholtz_of` with the leaf proofs
`rawEqOffAxis`, `exactPresDecay`, `liftPExt`, `liftPDecay`, `dmuDivFreeSol`, `rbExt`, and
`dmuChgLin`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`presHelmholtz`** (`PartIII-b:C/rep/8/2/pres/3/2/1`, source 5245-5260, 5272-5281,
1213-1225, 4139-4141): the pressure Helmholtz identity along the sequence. -/
theorem presHelmholtz (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.PresHelmholtz :=
  D.presHelmholtz_of hst (rawEqOffAxis D hst) (exactPresDecay D hst) (liftPExt D hst)
    (liftPDecay D hst) dmuDivFreeSol (rbExt D hst) (dmuChgLin D hst)

end UnforcedLeray.Short.PartIIIb.Concrete

end
