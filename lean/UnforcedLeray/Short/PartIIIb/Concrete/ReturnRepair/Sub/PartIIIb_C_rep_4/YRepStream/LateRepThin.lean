import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.Reduce
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.FarKernel

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem lateRepThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : LateRepThin Pl σ₀ mZ dm dp := by
  exact lateRepThin_of_farRepThinUng Pl σ₀ mZ dm dp (farRepThinUng Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
