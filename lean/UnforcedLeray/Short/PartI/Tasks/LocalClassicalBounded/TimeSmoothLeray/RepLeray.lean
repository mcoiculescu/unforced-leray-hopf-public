import UnforcedLeray.Short.PartI.Sub.T02_1_4_6
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.DivFreeTestClass
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.LaplacianTestClosed
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.SeedGenerator
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.TimeDerivUnderIntegral
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.LaplacianIBP
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.ResidualPairingSplit
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepSolenoidal

/-!
# Part I, task `PartI:T02/1/4/6`: assembly of `RepLeray`

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `RepLeray` (`Short/PartI/Sub/T02_1_4.lean`). Applies `repLeray_of`
(`Short/PartI/Sub/T02_1_4_6.lean`) to the seven leaf theorems and `repSolenoidal`.
No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem repLeray : RepLeray :=
  repLeray_of divFreeTestClass laplacianTestClosed repSolenoidal seedGenerator stressGenerator
    timeDerivUnderIntegral laplacianIBP residualPairingSplit

end UnforcedLeray.Short.PartI
