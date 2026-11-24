import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1_3
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.PhaseTConj

/-!
# Part II-a, task `PartII-a:F09/1/3/1/3`: `PhaseDualityAdjT`

Source `the November 2 reference manuscript` lines 1403-1413, 1426-1428.
Immediate from `phaseDualityAdjT_of` (duality from the conjugation-commutation of `𝒯(s)`) and the
sibling task `PartII-a:F09/1/3/1/3/1` (`phaseTConj`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **Task `PartII-a:F09/1/3/1/3`**: Hilbert duality of the phase semigroup on a phase test. -/
theorem phaseDualityAdjT : PhaseDualityAdjT :=
  phaseDualityAdjT_of phaseTConj

end UnforcedLeray.Short.PartIIa
