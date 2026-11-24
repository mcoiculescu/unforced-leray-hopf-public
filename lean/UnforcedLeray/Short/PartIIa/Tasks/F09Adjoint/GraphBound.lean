import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Laplacian
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Energy

/-!
# Part II-a, task `PartII-a:F09/3`: the adjoint graph bound

Source `the November 2 reference manuscript`
lines 1426-1442 (time-reversed diffusion bound) and 1491-1496 (Hilbert identity on `D_2`).

Composes the two leaves `adjointLaplacianBound` (task `PartII-a:F09/3/1`,
Tasks/F09Adjoint/GraphBound/Laplacian.lean) and `adjointEnergyD2` (task `PartII-a:F09/3/2`,
Tasks/F09Adjoint/GraphBound/Energy.lean) through `adjointGraphBound_of` (Sub/PartII-a_F09_3.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F09/3`: the adjoint graph bound.** -/
theorem adjointGraphBound : AdjointGraphBound :=
  adjointGraphBound_of adjointLaplacianBound adjointEnergyD2

end UnforcedLeray.Short.PartIIa
