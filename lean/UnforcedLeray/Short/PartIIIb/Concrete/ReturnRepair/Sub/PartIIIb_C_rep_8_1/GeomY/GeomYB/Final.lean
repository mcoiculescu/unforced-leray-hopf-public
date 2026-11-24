import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitive
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth

/-!
# `PartIII-b:C/rep/8/1/1/2/5`: assembly of `D.GeomYB`

Composition of `SeqData.geomYB_of_bounds` (`GeomYB.lean`) with `phasePrimitiveYBBound`
(`GeomYB/PhasePrimitive.lean`) and `taylorWidthYBBound` (`GeomYB/TaylorWidth.lean`).
Source `the November 2 reference manuscript`
lines 5427-5432, 4195-4215, 5383-5387.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem geomYB (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.GeomYB :=
  D.geomYB_of_bounds hst (phasePrimitiveYBBound D hst) (taylorWidthYBBound D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
