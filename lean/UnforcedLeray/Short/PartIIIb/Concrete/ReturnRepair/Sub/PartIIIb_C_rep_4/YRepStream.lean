import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.Margin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.ShiftedResolventRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem ageTransRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeTransRep Pl σ₀ mZ dm dp :=
  ageTransRep_of (transRepOpTable_of (sepYoungRep dm dp) (shiftedResolventRep dm dp) (transRepTable Pl σ₀ mZ dm dp))

end UnforcedLeray.Short.PartIIIb.Concrete
