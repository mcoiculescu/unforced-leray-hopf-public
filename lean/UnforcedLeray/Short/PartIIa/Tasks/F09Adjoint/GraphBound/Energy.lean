import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_2
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.GradLimit
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense

/-!
# Part II-a, task `PartII-a:F09/3/2`: the adjoint Hilbert identity on `D_2`

Source `the November 2 reference manuscript`
lines 1424-1450 (smooth core of `D_2`) and 1491-1496 (the Hilbert identity).

`adjointEnergyD2_of` (Sub/PartII-a_F09_3_2.lean) reduces `AdjointEnergyD2` to the core density
`d2CoreDense` (task `PartII-a:F14/1/1`, Tasks/F14SmoothStressMap/CoreDense.lean) and the
gradient-limit lemma `d2GradLimit` (Tasks/F09Adjoint/GraphBound/GradLimit.lean, task
`PartII-a:F09/3/2/1`). Both are accepted; this file composes them.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F09/3/2`: the adjoint Hilbert identity on `D_2`.** -/
theorem adjointEnergyD2 : AdjointEnergyD2 :=
  adjointEnergyD2_of d2CoreDense d2GradLimit

end UnforcedLeray.Short.PartIIa
