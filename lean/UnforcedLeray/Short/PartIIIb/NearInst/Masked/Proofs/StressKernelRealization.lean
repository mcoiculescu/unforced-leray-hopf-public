import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.KernelFormulaSmooth
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.ChartConjSmooth
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.DensityBox

/-!
# `stressKernelRealization : StressKernelRealization` (`PartIII-b:C/near/masked/18`)

Assembly of the three proved steps `kernelFormulaSmooth`, `chartConjSmooth`, `densityBox` through
`stressKernelRealization_of` (`Realization/Sub.lean`).  Source 1548-1575, 1639-1689, 2681-2691,
3586-3626, 3893-3921 (see `Realization/Sub.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- **`StressKernelRealization`**: every real form of a stress map acts on box inputs by the
unmasked kernel `fullOut`, from the three steps `KernelFormulaSmooth`, `ChartConjSmooth`,
`DensityBox`. -/
theorem stressKernelRealization : StressKernelRealization :=
  Realization.stressKernelRealization_of
    Realization.kernelFormulaSmooth
    Realization.chartConjSmooth
    _root_.densityBox

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
