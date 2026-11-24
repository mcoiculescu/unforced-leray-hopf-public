import UnforcedLeray.Short.PartIIa.Sub.F06
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian

/-!
# Part II-a, task `PartII-a:F06`: the common body graph bound

Source of record: `the November 2 reference manuscript`, lines 1353-1355 and
the proof 1363-1480. The quantitative body diffusion bound `bodyLaplacianBound` (task `PartII-a:F06/1`)
feeds `commonBodyGraphBound_of` (proved in `Sub/F06.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F06`**: the common body graph bound. -/
theorem commonBodyGraphBound : CommonBodyGraphBound :=
  commonBodyGraphBound_of bodyLaplacianBound

end UnforcedLeray.Short.PartIIa
