import UnforcedLeray.Short.Interface.WindowSteps2
import UnforcedLeray.Short.Interface.Leaf4a_Chart13
import UnforcedLeray.Short.Interface.Leaf4a_Time14
import UnforcedLeray.Short.Interface.Leaf4a_L2
import UnforcedLeray.Short.Interface.Leaf4a_Back
import UnforcedLeray.Short.Interface.Leaf4a_Source.Assemble

/-!
# Interface: leaf 4a, the window estimate in source form (task `Interface:I17`)

Unconditional assembly of `SourceWindowRegularity` (`Short/Interface/WindowSteps.lean`) from the
four window steps, each proved in its own task: `windowChartEquationLocal` (`Interface:I12`),
`windowChartTimeChange` (`Interface:I13`), `windowChartL2` (`Interface:I14`) and
`windowTransportBack` (`Interface:I15`). The argument is `sourceWindowRegularity_of`
(`Leaf4a_Source/Assemble.lean`, compiled).

Status: compiled; the four imported modules are accepted and unconditional.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Interface

/-- Leaf 4a: the window estimate in source form (`eq:free-stress-13`-`-17`, `q = 2`). -/
theorem sourceWindowRegularity : SourceWindowRegularity :=
  sourceWindowRegularity_of windowChartEquationLocal windowChartTimeChange windowChartL2
    windowTransportBack

end UnforcedLeray.Short.Interface
