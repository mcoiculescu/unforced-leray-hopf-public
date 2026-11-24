import UnforcedLeray.Short.PartI.Sub.PartI_S05_1_1

/-!
# Part I, task `PartI:S05/1`: the target `gaussianModeLaplacian_proof`

Target: `gaussianModeLaplacian_proof : GaussianModeLaplacian`, source lines 788-803 of
`the November 2 reference manuscript`.

This file closes the target by composing the reduction `gaussianModeLaplacian_of_core`
(`PartI_S05_1.lean`) with the polar identity `polarLaplacianCore_proof` (`PartI_S05_1_1.lean`).
It sits in a separate file because `PartI_S05_1_1.lean` imports `PartI_S05_1.lean`, so the
theorem cannot be appended to `PartI_S05_1.lean` without creating an import cycle.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target.** The planar Laplacian of every Gaussian growing mode equals `q`. -/
theorem gaussianModeLaplacian_proof : UnforcedLeray.Short.PartI.GaussianModeLaplacian :=
  gaussianModeLaplacian_of_core polarLaplacianCore_proof

end UnforcedLeray.Short.PartI

end
