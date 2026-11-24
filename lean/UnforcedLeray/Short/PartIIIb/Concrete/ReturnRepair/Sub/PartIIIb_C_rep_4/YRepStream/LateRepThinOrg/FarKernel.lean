import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.FarKernel.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.StrBoxTrunc
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarOutChartQ
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarOutPointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.EtaQSupSeq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarRecvIntegral

/-!
# `PartIII-b:C/rep/4/4/1/org/5/1`: `farRepThinUng`

Source `the November 2 reference manuscript` 5303-5306, 3902-3920, 3621,
3593-3594, 5323-5338, 5345-5355.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The ungained far-kernel bound for the repair-to-thin entry** (source 5303-5306, 3902-3920,
3621, 3593-3594, 5323-5338, 5345-5355). -/
theorem farRepThinUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarRepThinUng Pl σ₀ mZ dm dp :=
  farRepThinUng_of_leaves Pl σ₀ mZ dm dp strBoxTrunc (sopSubIsFarSeq Pl σ₀ mZ dm dp)
    farOutChartQ farOutPointwise (etaQSupSeq dm dp) farRecvIntegral

end UnforcedLeray.Short.PartIIIb.Concrete
