import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_Lem
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_3_2_1_6_2

/-!
# `liftPDecay` (`PartIII-b:C/rep/8/2/pres/3/2/1/6`): decay of the lifted pressure `p_lift`

Source of record: `the November 2 reference manuscript`
(73 pages): 1202 (bounded train pressure), 1213-1225, 2541-2552, 2697-2713, 5274-5276.

Proves `liftPDecay` by combining `liftPDecay_of_regions` with `liftPPointwise_young` and
`liftPPointwise_old`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem liftPDecay (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.LiftPDecay :=
  liftPDecay_of_regions D (liftPPointwise_young D hst) (liftPPointwise_old D hst)

end UnforcedLeray.Short.PartIIIb.Concrete

end
