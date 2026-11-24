import UnforcedLeray.Short.Interface.Compose
import UnforcedLeray.Short.Interface.Leaf1
import UnforcedLeray.Short.Interface.Leaf2
import UnforcedLeray.Short.Interface.Leaf3
import UnforcedLeray.Short.Interface.Leaf4a_Source
import UnforcedLeray.Short.Interface.Leaf4a_Reduce
import UnforcedLeray.Short.Interface.Leaf4b

/-!
# Interface: final discharge of the interface bundle (task `Interface:I22`)

The five unconditional leaves of `Statements.lean` form the bundle `InterfaceLeaves`
(`Compose.lean`), and `mainClaim_of_constructionClaimShort` turns it into
`ConstructionClaimShort → MainClaim`. So Theorem A reduces to `ConstructionClaimShort` alone,
that is, to the shorter proof's Parts I-III (`the November 2 reference manuscript`,
lines 143-187 for the energy class and lines 6064-6075 for the regular background).

Leaf sources:
* `path`: `l3BackgroundOfPath` (`Leaf1.lean`, task `Interface:I03`);
* `toLine`: `periodicModeEquationToLine` (`Leaf2.lean`, task `Interface:I11`);
* `bodyForce`: `bodyForceL3` (`Leaf3.lean`, task `Interface:I05`);
* `window`: `windowReduction sourceWindowRegularity` (`Leaf4a_Reduce.lean`, `Interface:I16`, applied
  to `sourceWindowRegularity` from `Leaf4a_Source.lean`, `Interface:I17`);
* `patch`: `windowsToGlobalLaplacian` (`Leaf4b.lean`, task `Interface:I21`).

This module supplies the five leaves to the interface composition.
The conditional form `mainClaim_of_constructionClaimShort_final_of`
is in `Sub/I22.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Interface

open UnforcedLeray.Blueprint

/-- The five leaves of the bridge, from the unconditional leaf theorems. -/
theorem interfaceLeaves : InterfaceLeaves :=
  ⟨l3BackgroundOfPath, periodicModeEquationToLine, bodyForceL3,
    windowReduction sourceWindowRegularity, windowsToGlobalLaplacian⟩

/-- **Final discharge**: `ConstructionClaimShort → MainClaim`, with no leaf left open. -/
theorem mainClaim_of_constructionClaimShort_final :
    ConstructionClaimShort → UnforcedLeray.MainClaim :=
  mainClaim_of_constructionClaimShort interfaceLeaves

end UnforcedLeray.Short.Interface

#print axioms UnforcedLeray.Short.Interface.mainClaim_of_constructionClaimShort_final
