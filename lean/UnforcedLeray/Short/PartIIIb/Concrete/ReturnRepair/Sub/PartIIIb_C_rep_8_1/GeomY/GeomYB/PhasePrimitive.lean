import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitive.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf

/-!
# `PartIII-b:C/rep/8/1/1/2/5/1`: assembly of `D.PhasePrimitiveYBBound`

Composition of `YBPhase.phasePrimitiveYBBound_of` (`PhasePrimitive/Of.lean`) with the commutator
oscillation leaf `YBPhase.sepCommOscFar` (`PhasePrimitiveLeaf.lean`).
Source `the November 2 reference manuscript`
lines 5427-5432, 4195-4215, 5400-5427.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phasePrimitiveYBBound (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    D.PhasePrimitiveYBBound :=
  YBPhase.phasePrimitiveYBBound_of YBPhase.sepCommOscFar D hst

end UnforcedLeray.Short.PartIIIb.Concrete
