import UnforcedLeray.Short.PartI.Sub.PartI_S05
import UnforcedLeray.Short.PartI.Sub.PartI_S05_1_proof

/-!
# Part I, task `PartI:S05`: the target `seedModeRegularity_proof`

Target: `seedModeRegularity_proof : SeedModeRegularity`, regularity and decay of the growing mode
(source lines 593-601 and 758-808 of `the November 2 reference manuscript`).

Proof: the conditional theorem `seedModeRegularity_of` (`PartI_S05.lean`) applied to the
planar Laplacian identity `gaussianModeLaplacian_proof` (`PartI_S05_1_proof.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target.** Regularity and decay of the Gaussian growing mode. -/
theorem seedModeRegularity_proof : SeedModeRegularity :=
  seedModeRegularity_of gaussianModeLaplacian_proof

end UnforcedLeray.Short.PartI

end
