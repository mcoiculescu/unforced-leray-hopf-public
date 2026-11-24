import UnforcedLeray.Short.Interface.Sub.I21
import UnforcedLeray.Short.Interface.Leaf4b_Glue
import UnforcedLeray.Short.Interface.Leaf4b_Periodic

/-!
# Interface leaf 4b (`WindowsToGlobalLaplacian`): the unconditional statement

Task `Interface:I21`. Source of record: `the November 2 reference manuscript`
does not state the window argument; the old manuscript `paper/main.tex` lines 7519-7536 do.

The two hypotheses of the conditional assembly `windowsToGlobalLaplacian_of` (`Sub/I21.lean`) are
proved elsewhere: `windowGlueLocal : WindowGlueLocal` (I19, `Leaf4b_Glue.lean`) and
`periodicSelection : PeriodicSelection` (I20, `Leaf4b_Periodic.lean`). This file only assembles
them, with no new hypotheses.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Interface

/-- **Leaf 4b, patching the windows** (`WindowsToGlobalLaplacian`, `Statements.lean`): the window
Laplacians of the free equation glue to a global `𝒴₂` Laplacian. Proved unconditionally by the
gluing step `windowGlueLocal` and the periodic selection `periodicSelection`, through the
conditional assembly `windowsToGlobalLaplacian_of`. -/
theorem windowsToGlobalLaplacian : WindowsToGlobalLaplacian :=
  windowsToGlobalLaplacian_of windowGlueLocal periodicSelection

end UnforcedLeray.Short.Interface
