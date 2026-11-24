import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf1.H
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf1.Formula
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf1.Calc
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf2.Fubini

/-!
# Part II-b, task `PartII-b:G4/2/1/2/2` (`greenSqVolterra`) assembly

Source: `the November 2 reference manuscript`, lines 2347-2352.

Assembles the leaf `GreenSqVolterra` from `greenSqH` (`Leaf1/H.lean`), `greenSqFormula`
(`Leaf1/Formula.lean`), `sqFCalculus` (`Leaf1/Calc.lean`) and `sqFubini` (`Leaf2/Fubini.lean`)
through `greenSqVolterra_of` of `Sub.G4_2_1_2_2`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem greenSqVolterra : UnforcedLeray.Short.IIb.GreenSqVolterra :=
  greenSqVolterra_of greenSqH greenSqFormula sqFCalculus sqFubini

end UnforcedLeray.Short.IIb
