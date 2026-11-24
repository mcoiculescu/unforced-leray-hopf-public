import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.RABoundExists
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.RhoW1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_9.AffMJet
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ActualJet

/-!
# `PartIII-b:C/rep/9`: Actual-jet affine remainder (`D.AffineRemainder`)

Source: `the November 2 reference manuscript` lines 5507-5525, 5694.
Assembles `affineRemainder` from `affineRemainder_of`, `repairStanding_rABoundExists`,
`repairStanding_rhoW1`, `affMJet_of`, and `actualJet` (`C/rep/6`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem affineRemainder (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.AffineRemainder := by
  exact affineRemainder_of D hst (repairStanding_rABoundExists D hst)
    (repairStanding_rhoW1 D hst) (affMJet_of D hst (actualJet D hst))

end UnforcedLeray.Short.PartIIIb.Concrete
