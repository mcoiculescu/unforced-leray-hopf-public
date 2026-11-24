import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.FarVelYoungBox
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Extend
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

theorem farRepRepUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarRepRepUng Pl σ₀ mZ dm dp :=
  farRepRepUng_of Pl σ₀ mZ dm dp (sopSubIsFarSeq Pl σ₀ mZ dm dp) farVelYoungBox (repRecvConv dm dp) farRepExtend

end UnforcedLeray.Short.PartIIIb.Concrete
