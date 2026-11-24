import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2_1
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2_2
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2_3

/-!
# Part I, task `PartI:T02/1/4/6/4/2`: unconditional `centeredHeatAgeDerivative`

Closes `centeredHeatAgeDerivative : CenteredHeatAgeDerivative` from the three leaf proofs
`leafAgeWeightedCH_proof` (`Sub/T02_1_4_6_4_2_1.lean`), `leafAgeIBPCH_proof`
(`Sub/T02_1_4_6_4_2_2.lean`) and `leafShiftLapCH_proof` (`Sub/T02_1_4_6_4_2_3.lean`), via the
conditional assembly `centeredHeatAgeDerivative_of_leaves` (`Sub/T02_1_4_6_4_2.lean`).
No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem centeredHeatAgeDerivative : CenteredHeatAgeDerivative :=
  centeredHeatAgeDerivative_of_leaves leafAgeWeightedCH_proof leafAgeIBPCH_proof
    leafShiftLapCH_proof

end UnforcedLeray.Short.PartI
