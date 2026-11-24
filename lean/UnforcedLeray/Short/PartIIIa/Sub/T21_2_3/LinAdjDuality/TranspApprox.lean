import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.TestApprox
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox.KernelVel

/-!
# `PartIII-a:T21/2/3/1/9/1`: `ladTranspApprox` (`LadTranspApprox`)

Source `the November 2 reference manuscript` lines 3230-3240 and 3052-3058.

Assembly: `ladTranspApprox_of` (parent decomposition file) applied to
`ladTestDensity` (`LadTestDensity`, from `TranspApprox/TestApprox.lean`, which already
combines the density and circulation-repair leaves) and `ladKernelVel` (`LadKernelVel`,
from `TranspApprox/KernelVel.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- `LadTranspApprox m` from the test-density and kernel-velocity leaves. -/
theorem ladTranspApprox (m : ℝ) (hm : 8 < m) : LadTranspApprox m :=
  ladTranspApprox_of m hm (ladTestDensity m hm) ladKernelVel

end UnforcedLeray.Short.IIIa
