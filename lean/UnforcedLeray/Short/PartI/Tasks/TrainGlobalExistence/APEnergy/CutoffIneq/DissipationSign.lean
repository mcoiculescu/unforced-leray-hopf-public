import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_3
import UnforcedLeray.Short.PartI.Sub.T05b_2

/-!
# Part I, task `PartI:T04/5/1/3/1`: dissipation sign in the cutoff energy identity

Target: `apEnergyDissipationSign : APEnergyDissipationSign` (`Short/PartI/Sub/PartI_T04_5_1_3.lean`).
Source of record: `the November 2 reference manuscript`, lines 278-286.

The integrand is `χ_R |∇v|²` with `χ_R = etaCutoff R ≥ 0` and `gradNormSq ≥ 0`, so the cell
integral is nonnegative; `integral_nonneg` needs no integrability.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **Leaf 1 (dissipation sign)**: `∫_cell χ_R |∇v|² ≥ 0`. -/
theorem apEnergyDissipationSign : APEnergyDissipationSign := by
  intro ν c T v p hν hc hcls R hR s
  exact integral_nonneg (fun z => mul_nonneg (etaCutoff_nonneg R z.2) (gradNormSq_nonneg _ z))

end UnforcedLeray.Short.PartI
