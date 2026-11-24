import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Product

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem earlyRepThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : EarlyRepThin Pl σ₀ mZ dm dp := by
  exact earlyRepThin_of Pl σ₀ mZ dm dp (earlyRepThinKernel Pl σ₀ mZ dm dp) (earlyRepThinProduct Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
