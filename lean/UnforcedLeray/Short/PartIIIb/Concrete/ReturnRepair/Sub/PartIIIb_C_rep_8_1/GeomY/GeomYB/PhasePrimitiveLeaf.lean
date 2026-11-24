import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitive.Of
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.CommDerivSplit
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.SepX0OscFar0
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.SepX0OscFar2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.PhasePrimitiveLeaf.SepPsiOscFar

/-!
# `PartIII-b:C/rep/8/1/1/2/5/1/1` (`GeomYB.PhasePrimitiveLeaf`): phase primitive for the commutator

Source `the November 2 reference manuscript`
lines 5427-5432, 4195-4215, 5400-5427, 3700-3712.

Assembles `YBPhase.sepCommOscFar : SepCommOscFar` from `YBPhase.sepCommOscFar_of` and the four
transition-annulus sub-leaves `YBPhase.commDerivSplit`, `YBPhase.sepX0OscFar0`,
`YBPhase.sepX0OscFar2`, and `YBPhase.sepPsiOscFar` (`SepX0OscFar1` is already discharged by
`sepX0OscFar1` in `PhasePrimitiveLeaf/Defs.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace YBPhase

open YBComm PhasePrim

/-- **`SepCommOscFar` from the four remaining transition-annulus sub-leaves**
(`SepX0OscFar1` is already discharged by `sepX0OscFar1` in `PhasePrimitiveLeaf/Defs.lean`). -/
theorem sepCommOscFar_of (hSplit : CommDerivSplit) (h0 : SepX0OscFar0)
    (h2 : SepX0OscFar2) (hPsi : SepPsiOscFar) : SepCommOscFar :=
  sepCommOscFarFixed_of hSplit h0 h2 hPsi

end YBPhase

open YBPhase
export YBPhase (SepCommOscFar)

/-- **Leaf: phase primitive for the commutator** (`PartIII-b:C/rep/8/1/1/2/5/1/1`,
source 5427-5432, 4195-4215, 5400-5427). -/
theorem YBPhase.sepCommOscFar : SepCommOscFar :=
  YBPhase.sepCommOscFar_of YBPhase.commDerivSplit YBPhase.sepX0OscFar0
    YBPhase.sepX0OscFar2 YBPhase.sepPsiOscFar

end UnforcedLeray.Short.PartIIIb.Concrete
