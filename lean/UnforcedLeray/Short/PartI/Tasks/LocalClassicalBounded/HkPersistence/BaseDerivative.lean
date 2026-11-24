import UnforcedLeray.Short.PartI.Sub.T02_1_2_4
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative.WeightedEstimate
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative.Additive
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative.Dense
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.BaseDerivative.Closed

/-!
# Part I, task `PartI:T02/1/2/4`: `BaseDerivative` (final assembly)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepcevic 2015, Theorem 1.1: smoothness for positive time and the datum in `BUC ∩ H^k`;
here the first derivative of the mild `H^3` solution).

The target `BaseDerivative` (`Short/PartI/Sub/T02_1_2.lean`) is obtained from the conditional
theorem `baseDerivative_of_leaves` (`Short/PartI/Sub/T02_1_2_4.lean`) by supplying its five
hypotheses:

1. `bilDuhamelDerivative` (product rule, task `PartI:T02/1/2/3`, `HkPersistence/ProductRule.lean`);
2. `bilDuhamelAdditive` (leaf A, `HkPersistence/BaseDerivative/Additive.lean`);
3. `bilWeightedEstimate` (leaf W, `HkPersistence/BaseDerivative/WeightedEstimate.lean`);
4. `derivDense` (leaf D, `HkPersistence/BaseDerivative/Dense.lean`);
5. `derivClosed` (leaf C, `HkPersistence/BaseDerivative/Closed.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Task `PartI:T02/1/2/4`: `BaseDerivative`.** Final assembly from the product rule and the four
leaves; see `baseDerivative_of_leaves`. -/
theorem baseDerivative : BaseDerivative :=
  baseDerivative_of_leaves bilDuhamelDerivative bilDuhamelAdditive bilWeightedEstimate
    derivDense derivClosed

end UnforcedLeray.Short.PartI
