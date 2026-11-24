import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.StrBoxTrunc
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.FarVelYoungBoxL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRepOrg.ThinLiftZ1

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem farLateThinRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarLateThinRep Pl σ₀ mZ dm dp :=
  farLateThinRep_of_leaves Pl σ₀ mZ dm dp strBoxTrunc (sopSubIsFarSeq Pl σ₀ mZ dm dp) farVelYoungBoxL2 (repRecvConv dm dp) thinLiftZ1

end UnforcedLeray.Short.PartIIIb.Concrete
