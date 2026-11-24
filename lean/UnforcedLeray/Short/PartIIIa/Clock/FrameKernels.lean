import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_3
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4
import UnforcedLeray.Short.PartI.Tasks.SeedModeRegularityProof
import UnforcedLeray.Short.PartI.Tasks.SeedFunctionalProof

/-!
# Part III-a, task `PartIII-a:T21/c1/a`: existence of the planar frame kernels

Source: `the November 2 reference manuscript`, lines 593-610 and 2891-2897.

Assembles `planarFrameKernelsExist_of` (Sub/T21_c1_a.lean) from the proved Part I seed
statements (`PartI.seedModeRegularity_proof`, `PartI.seedFunctional_proof`) and the four
proved leaves (`seedSmoothRep_proof`, `seedGaussHalf_proof`, `seedDualKernel_proof`,
`seedBiorth_proof`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem planarFrameKernelsExist : UnforcedLeray.Short.IIIa.PlanarFrameKernelsExist :=
  UnforcedLeray.Short.IIIa.planarFrameKernelsExist_of
    UnforcedLeray.Short.PartI.seedModeRegularity_proof
    UnforcedLeray.Short.PartI.seedFunctional_proof
    seedSmoothRep_proof seedGaussHalf_proof seedDualKernel_proof seedBiorth_proof

end UnforcedLeray.Short.IIIa
