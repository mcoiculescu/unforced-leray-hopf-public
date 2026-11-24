import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_cont_WE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardDXSubYoungL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardD2XSubYoungL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardDYSubYoungL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardDXSubYoungSup
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2

/-!
# `PartIII-b:C/cont/WE`: continuity of the Ward residual map `μ ↦ (wardOps Pl K L μ).2.2`

Source of record: `the November 2 reference manuscript`
(73 pages), lines 4161-4303 (`subsec:ward`), 5196-5260 (`prop:actual-body`), 5684-5685, 5701-5704,
5918-5920.

Decomposed in `UnforcedLeray.Short.«PartIII-b».Sub.«PartIII-b_C_cont_WE»` (and
`UnforcedLeray.Short.«PartIII-b».Concrete.ReturnRepair.Continuity.WardE.Defs`) via
`wardECont_of_leaves` into the four `μ`-Lipschitz young-support leaves:
* `WardDXSubYoungL2` (`PartIII-b:C/cont/WE/1`),
* `WardD2XSubYoungL2` (`PartIII-b:C/cont/WE/2`),
* `WardDYSubYoungL2` (`PartIII-b:C/cont/WE/3`),
* `WardDXSubYoungSup` (`PartIII-b:C/cont/WE/4`),
together with `BgYoungW2` (`PartIII-b:C/ward/12`) and `BgPresY2B` (`PartIII-b:C/ward/13`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Conditional assembly of `SeqData.wardECont` (`PartIII-b:C/cont/WE`) from the leaf obligations
in `Sub/PartIII-b_C_cont_WE.lean`. -/
theorem SeqData.wardECont_of_leaves (hX : WardDXSubYoungL2) (hX2 : WardD2XSubYoungL2)
    (hDY : WardDYSubYoungL2) (hsup : WardDXSubYoungSup)
    (hY : BgYoungW2) (hP : BgPresY2B)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.WardECont :=
  UnforcedLeray.Short.PartIIIb.Concrete.wardECont_of_leaves hX hX2 hDY hsup hY hP D hst

theorem SeqData.wardECont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.WardECont :=
  wardECont_of_leaves wardDXSubYoungL2_proved wardD2XSubYoungL2_proved
    wardDYSubYoungL2_proved wardDXSubYoungSup_proved bgYoungW2_proved bgPresY2B_proved D hst

end UnforcedLeray.Short.PartIIIb.Concrete
end
