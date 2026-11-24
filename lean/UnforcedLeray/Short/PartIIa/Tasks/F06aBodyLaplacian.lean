import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F06_1
import UnforcedLeray.Short.PartIIa.Tasks.F03LocalWindow
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.GlobalFieldWindowBound
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.PeriodAverageBound
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.SliceIntegralYq
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.LaplacianFieldToYRep
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.YqRepNorm
import UnforcedLeray.Short.PartIIa.Tasks.F06aBodyLaplacian.NormFromPower

/-!
# Part II-a, task `PartII-a:F06/1`: the quantitative body diffusion bound

Source of record: `the November 2 reference manuscript`, lines 1431-1480.
Assembles the six leaves (`F06/1/1`-`F06/1/6`) and the local window estimate `F03`
into `bodyLaplacianBound_of` (`Sub/PartIIa_F06_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F06/1`**: the quantitative body diffusion bound `BodyLaplacianBound`. -/
theorem bodyLaplacianBound : BodyLaplacianBound :=
  bodyLaplacianBound_of localWindowEstimate globalFieldWindowBound periodAverageBound
    sliceIntegralYq laplacianFieldToYRep yqRepNorm normFromPower

end UnforcedLeray.Short.PartIIa
