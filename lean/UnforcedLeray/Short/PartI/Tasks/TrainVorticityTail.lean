import UnforcedLeray.Short.PartI.Sub.PartI_T20
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail.AgeDeriv

/-!
# `PartI:T20` (`TrainVorticityTail.lean`): Gaussian transverse tail of the train vorticity

Source of record: `the November 2 reference manuscript`, lines 483-497, 523-526
(old 484-492), in the proof of Lemma `sct:heat`.

All proved components—uniform global vertical velocity decay (`train_v2_uniform_decay`), the
explicit drift primitive (`driftPrimitive`), the Gaussian supersolution and parabolic comparison at
`(ℓ, j) = (0, 0)` (`gaussSupersol_comparison`, `train_vorticity_gaussian_tail_zero_pointwise`,
`train_vorticity_gaussian_tail_zero`), the global polynomial bounds on spatial velocity and
vorticity jets (`PartI_T20.train_v_jet_sup_bound`, `PartI_T20.train_curl_derivWord_sup_bound`),
the 1D Landau-Kolmogorov ray interpolation (`PartI_T20.deriv_abs_le_three_sqrt_of_ray`), the
unconditional proof of the `ℓ = 0`, arbitrary `j : ℕ` spatial-jet Gaussian vorticity tail
(`train_vorticity_spatial_jet_tail : TrainOverlap → TrainVorticitySpatialJetTail`), the
age-derivative induction leaf (`TrainVorticityAgeDerivFromZero`, `PartI:T20/1`), and the
conditional assembly (`train_vorticity_gaussian_tail_of`)—are in
`UnforcedLeray.Short.PartI.Sub.PartI_T20`.

Once `PartI:T20/1` (`trainVorticityAgeDerivFromZero_proof : TrainVorticityAgeDerivFromZero`) is
proved in `UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail.AgeDeriv`, the unconditional theorem
`train_vorticity_gaussian_tail (hOv : TrainOverlap) : TrainVorticityGaussianTail` is obtained by
`train_vorticity_gaussian_tail_of trainVorticityAgeDerivFromZero_proof hOv`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Gaussian transverse tail of the train vorticity (`PartI:T20`)**:
source lines 483-497, 523-526 of `the November 2 reference manuscript`. -/
theorem train_vorticity_gaussian_tail (hOv : TrainOverlap) : TrainVorticityGaussianTail :=
  train_vorticity_gaussian_tail_of trainVorticityAgeDerivFromZero_proof hOv

end UnforcedLeray.Short.PartI

