import UnforcedLeray.Short.PartIIa.Sub.F03_1
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.RepLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.PeriodizedPairing
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.LocalIdentityOfPhaseOp
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.WindowChartU
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.WindowChartF
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.WindowTestIdentity

/-!
# Part II-a, task `PartII-a:F03/1`: the transformed equation `WindowEquation` (unconditional)

Source of record: `the November 2 reference manuscript`, lines 1431-1434.
Assembles the six leaves proved in `Tasks/F03aWindowEquation/` into `windowEquation_of`
(`Sub/F03_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F03/1`**: the transformed equation `(∂_θ - νΔ_x) u_c = F_c` weakly on `ℝ × ℝ³`. -/
theorem windowEquation : WindowEquation :=
  windowEquation_of repLocInt localIdentityOfPhaseOp windowChartU windowChartF windowTestIdentity

end UnforcedLeray.Short.PartIIa
