import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.SepWSubDom
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.WardYTransSubDom
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardY.WardYWSubChart

/-!
# The leaf `WardYCont`: the Ward field `Y[T]` is norm continuous in `μ`
(source 4161-4303, 5684-5685, 5701-5704, 5918-5920)

Source of record: `the November 2 reference manuscript` (73 pages).

Assembles `SeqData.wardYCont` from the three leaves:
* `sepWSubDom_proved : SepWSubDom` (`WardY/SepWSubDom.lean`),
* `wardYTransSubDom_proved : SepWSubDom → WardYTransSubDom` (`WardY/WardYTransSubDom.lean`),
* `wardYWSubChart_proved : SepWSubDom → WardYWSubChart` (`WardY/WardYWSubChart.lean`),
via `wardYCont_of_leaves` (`WardY/Defs.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`WardYCont`** on the concrete sequence (source 4161-4303, 5684-5685, 5701-5704, 5918-5920):
for eventually all `n`, `μ ↦ (D.wardOps n μ).1` is operator-norm continuous on `D.win n`. -/
theorem SeqData.wardYCont (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.WardYCont :=
  wardYCont_of_leaves sepWSubDom_proved wardYTransSubDom_proved wardYWSubChart_proved D hst

end UnforcedLeray.Short.PartIIIb.Concrete
