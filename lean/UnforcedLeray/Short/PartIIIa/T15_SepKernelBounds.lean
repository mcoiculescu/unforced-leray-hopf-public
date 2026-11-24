import UnforcedLeray.Short.PartIIIa.Sub.T15
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.GaussSup
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatGDecay
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailIterated
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailBound
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailDiffBound
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailZero
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.Part2Calculus
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.Part2Congr

/-!
# Part III-a, task `PartIII-a:T15`: `sep:kernel` (unconditional assembly)

Target (`SeparatedKernels.lean`): `SepKernelBounds` (SP 3604-3610). The conditional theorem
`sepKernelBounds_of` (`Sub/T15.lean`) is applied to the seven analytic leaves, each proved in
`T15_SepKernelBounds/`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem sepKernelBounds : UnforcedLeray.Short.IIIa.SepKernelBounds :=
  sepKernelBounds_of heatGDecay heatTailIterated heatTailBound heatTailDiffBound heatTailZero
    part2Calculus part2Congr

end UnforcedLeray.Short.IIIa

end
