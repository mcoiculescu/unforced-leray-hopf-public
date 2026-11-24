import UnforcedLeray.Short.PartIIIa.StressInputs
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_2
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_3
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_9
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_10

/-!
# Part III-a, task `PartIII-a:T23`: stress coefficient and transverse bounds at an exact split

Source of record: `the November 2 reference manuscript`, lines 2664-2745
(`stress-short:coefficients` and `stress-short:transverse`).

Assembles `stressSpacesExactSplit : StressCoefficients ∧ StressTransverse` from:
* `stressCoefficients_of rawCoeffLate rawCoeffEarly inletCoeffBounds` (`T23_9`, `T23_1`, `T23_2`, `T23_3`),
* `stressTransverse_of rawTransverseTail inletTransverseTail` (`T23_10`, `T23_4`, `T23_5`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem stressSpacesExactSplit : UnforcedLeray.Short.IIIa.StressCoefficients ∧ UnforcedLeray.Short.IIIa.StressTransverse :=
  ⟨stressCoefficients_of rawCoeffLate rawCoeffEarly inletCoeffBounds,
   stressTransverse_of rawTransverseTail inletTransverseTail⟩

end UnforcedLeray.Short.IIIa
