import UnforcedLeray.Short.PartI.Sub.PartI_T21_2
import UnforcedLeray.Short.PartI.Sub.PartI_T21_2.InteriorStripBounds
import UnforcedLeray.Short.PartI.Sub.PartI_T21_2.FluctJetWSupNorm

/-!
# `PartI:T21/2` (`Sub/PartI_T21/WeightedJetBounds.lean`): weighted jet bounds for `(ψ - hmean ψ, hfluct v, v, ω, p)`

Source of record: `the November 2 reference manuscript`, lines 513-526.

Proves `trainWeightedJetBounds_proof : TrainWeightedJetBounds` by combining
`trainInteriorStripJetBounds_proof` (`PartI:T21/2/1`) and
`trainFluctJetWSupNormLe_proof` (`PartI:T21/2/2`) via
`trainWeightedJetBounds_of_interior_and_fluct`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target theorem (`PartI:T21/2`, source lines 513-526)**: polynomial-weighted `L^∞` and
cell-`L²` bounds for all spatial and age derivatives of `(ψ - hmean ψ, hfluct v, v, ω, p)`. -/
theorem trainWeightedJetBounds_proof (hOv : TrainOverlap) (hVort : TrainVorticityGaussianTail) (hTail : TrainStreamVelocityPressureTransverseTail) : TrainWeightedJetBounds :=
  trainWeightedJetBounds_of_interior_and_fluct
    (trainInteriorStripJetBounds_proof hOv hVort hTail)
    trainFluctJetWSupNormLe_proof
    hOv hVort hTail

end UnforcedLeray.Short.PartI
