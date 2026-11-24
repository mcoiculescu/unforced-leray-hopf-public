import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinRecv
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.ThinMultPin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarOutChartQ
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarOutPointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.EtaQSupSeq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin.Kernel.FarRecvIntegral

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

theorem farThinRecv (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : FarThinRecv Pl σ₀ mZ dm dp :=
  farThinRecv_of Pl σ₀ mZ dm dp thinMultPin farOutChartQ farOutPointwise (etaQSupSeq dm dp)
    farRecvIntegral

end UnforcedLeray.Short.PartIIIb.Concrete
