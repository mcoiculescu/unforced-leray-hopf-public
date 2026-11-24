import UnforcedLeray.Short.PartIIb.Sub.G4_2_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf1.H
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf1.Formula
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Smooth.GreenInverseSqSmooth.Leaf1.Calc

/-!
# Part II-b, task `PartII-b:G4/2/1/2/1/1`-`3` assembly (`greenSqContinuous`)

Source: `the November 2 reference manuscript`, lines 2347-2352.

Assembles the leaf `GreenSqContinuous` from the three compiled subs `greenSqH`
(`Leaf1/H.lean`), `greenSqFormula` (`Leaf1/Formula.lean`) and `sqFCalculus` (`Leaf1/Calc.lean`)
through `greenSqContinuous_of` of `Sub.G4_2_1_2_1`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem greenSqContinuous : UnforcedLeray.Short.IIb.GreenSqContinuous :=
  greenSqContinuous_of greenSqH greenSqFormula sqFCalculus

end UnforcedLeray.Short.IIb
