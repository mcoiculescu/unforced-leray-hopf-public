import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_cont_S
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.SopFam
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.SopRes
import UnforcedLeray.Short.PartIIa.Tasks.N01StressMaps
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapUnique
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapReal
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyRealForms
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HW
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.FreeWeakUniqueness

/-!
# The leaf `SopCont`: `S_μ` is norm continuous on the window (source 5701-5702, 1556-1583,
1675-1690, 3888-3890)

Source of record: `the November 2 reference manuscript` (73 pages).

Assembles `SeqData.sopCont` via `sopCont_of` (`Sub/PartIII-b_C_cont_S.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst

/-- **`SopCont`** on the concrete sequence (source 5701-5702, 1556-1583, 1675-1690, 3888-3890). -/
theorem SeqData.sopCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.SopCont :=
  sopCont_of
    (stressMapFamilyCont_of UnforcedLeray.Short.PartIIa.nearStressMapExists
      (Masked.stressMapUnique_of Masked.tensorTestDense Masked.tensorTestDivMem)
      (stressMapResolvent Masked.tensorTestDense Masked.tensorTestDivMem))
    (Masked.stressMapReal_of Body.tepsReal' Masked.tensorTestDense Masked.tensorTestDivMem)
    UnforcedLeray.Short.PartIIIb.stressMapWeakSolC
    NearInst.stressPairAE
    Masked.cpcHT_eq
    Masked.cpcInvH_eq
    Masked.cpcH_eq
    (fun hc hν hε hP hμ => freeWeakUniqueness hc hν hε hP hμ)
    D hst

end UnforcedLeray.Short.PartIIIb.Concrete
