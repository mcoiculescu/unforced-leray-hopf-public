import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.DensApprox
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.DensCircFix

/-!
# `PartIII-a:T21/2/3/1/9/1/1`: `ladTestDensity` (`LadTestDensity`)

Source `the November 2 reference manuscript` lines 3230-3240.

Assembly: `ladTestDensity_of` (in the parent decomposition file) applied to the two leaves
`ladDensApprox` (`LadDensApprox`, from `DensApprox.lean`) and `ladDensCircFix`
(`LadDensCircFix`, from `DensCircFix.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `LadTestDensity m` from the two leaves. -/
theorem ladTestDensity (m : ℝ) (hm : 8 < m) : LadTestDensity m :=
  ladTestDensity_of m (ladDensApprox m hm) (ladDensCircFix m hm)

end UnforcedLeray.Short.IIIa
