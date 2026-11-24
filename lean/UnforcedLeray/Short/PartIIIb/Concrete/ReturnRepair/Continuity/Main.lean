import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Compose
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Sop
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Rop
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.NearSN
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Lj
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.FA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.EA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.RA
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Lam

/-!
# `PartIII-b:C/cont/main`: concrete return norm continuity

Source of record: `the November 2 reference manuscript` (73 pages),
lines 5684-5685, 5701-5704, 5918-5920.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem returnNormContinuity_concrete (D : SeqData) {dm dp : ℝ}
    (hst : D.RepairStanding dm dp)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) :
    ConcreteReturnNormContinuity D G :=
  returnNormContinuity_concrete_of_standing D hst G
    (D.sopCont hst) (D.ropCont hst) (D.wardYCont hst) (D.wardECont hst)
    (D.nearSNCont hst) (D.ljCont hst) (D.faCont hst) (D.eaCont hst)
    (D.raCont hst) (D.lamCont hst)

end UnforcedLeray.Short.PartIIIb.Concrete
