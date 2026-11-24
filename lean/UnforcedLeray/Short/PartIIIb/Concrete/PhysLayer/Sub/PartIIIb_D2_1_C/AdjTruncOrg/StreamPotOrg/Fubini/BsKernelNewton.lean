import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Fubini.Defs
import UnforcedLeray.Analysis.Pressure.NewtonKernel

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bsKernelNewton : BSKernelNewton := by
  intro w i
  simp only [bsKernel, PiLp.toLp_apply, UnforcedLeray.PressureAnalysis.newtonGradientKernel]
  push_cast
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
