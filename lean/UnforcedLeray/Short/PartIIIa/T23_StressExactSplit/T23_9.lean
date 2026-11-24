import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_9
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_9.L1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_9.L2

/-!
# Part III-a, task `PartIII-a:T23/9`: `stress-short:coefficients`

Assembly of the stress-coefficient bounds (SP lines 2664-2745) from the raw-lift and inlet
bounds `RawCoeffLate`, `RawCoeffEarly`, `InletCoeffBounds` and the two measurability leaves
`etaProfileAEMeasurable` (T23/9/1) and `chartSliceMeasurable` (T23/9/2).
The bulk of the argument is `stressCoefficients_of_leaves` in `Sub/PartIII-a_T23_9`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem stressCoefficients_of (h1 : UnforcedLeray.Short.IIIa.RawCoeffLate) (h2 : UnforcedLeray.Short.IIIa.RawCoeffEarly) (h3 : UnforcedLeray.Short.IIIa.InletCoeffBounds) : UnforcedLeray.Short.IIIa.StressCoefficients :=
  UnforcedLeray.Short.IIIa.stressCoefficients_of_leaves h1 h2 h3 etaProfileAEMeasurable chartSliceMeasurable

end UnforcedLeray.Short.IIIa

end
