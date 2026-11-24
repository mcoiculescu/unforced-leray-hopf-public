import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.Margin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.NearYoungOld
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepThin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.EarlyRepRep

/-!
# `PartIII-b:C/rep/4/4/1/org/9`: the corrected repair far-region leaf

Source `the November 2 reference manuscript` 5303-5308, 5362-5372, 5617.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The late-output and early-source regions on repair sources (`margin 19γ/66`, source 5303-5308,
5362-5372, 5617). -/
theorem ageLateEarlyRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeLateEarlyRep Pl σ₀ mZ dm dp :=
  ageLateEarlyRep_of (nearYoungOld dm dp) (lateRepThin Pl σ₀ mZ dm dp)
    (lateRepRep Pl σ₀ mZ dm dp) (earlyRepThin Pl σ₀ mZ dm dp) (earlyRepRep Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
