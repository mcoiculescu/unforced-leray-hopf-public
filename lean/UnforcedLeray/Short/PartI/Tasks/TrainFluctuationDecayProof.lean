import UnforcedLeray.Short.PartI.Sub.PartI_T22
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecay.PostOverlapStreamPressureZero
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecay.PostOverlapAgeDeriv

/-!
# `PartI:T22`: exponential fluctuation decay in all polynomial weights (`sct:fluctuation`)

Source of record: `the November 2 reference manuscript`, lines 439-446, 515-526.

The weight interpolation (`PartI_T22.wSupNorm_interp`, `PartI_T22.wCellL2_interp`), pre-overlap
exponential bound (`PartI_T22.polyPS_le_polyP_mul_exp_of_le_overlapAge`), polynomial-in-age
absorption (`PartI_T22.polyPS_mul_exp_absorb`), unconditional `ℓ = 0` velocity post-overlap
fluctuation decay (`trainPostOverlapVelZero_of`), and conditional assembly
(`trainFluctuationDecay_of`) are proved in `UnforcedLeray.Short.PartI.Sub.PartI_T22`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainFluctuationDecay_proof (hTails : TrainStreamVelocityPressureTails) (hFD : OverlapFluctuationDecay) (hOv : TrainOverlap) : TrainFluctuationDecay := by
  exact trainFluctuationDecay_of hTails hFD hOv (trainPostOverlapStreamPressureZero_proof hTails hFD hOv) (trainPostOverlapAgeDerivFromZero_proof hTails)

end UnforcedLeray.Short.PartI

