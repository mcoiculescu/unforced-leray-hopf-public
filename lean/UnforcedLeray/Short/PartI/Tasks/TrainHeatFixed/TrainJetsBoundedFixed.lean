import UnforcedLeray.Short.PartI.Sub.PartI_HF_1
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay.DuhamelSplit
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed.PressStep

/-!
# `Short/PartI/Tasks/TrainHeatFixed/TrainJetsBoundedFixed.lean` — Task `PartI:HF/1`

Source of record: `the November 2 reference manuscript`, lines 427–435, 326–359,
318–322, 255–258.

Decomposed via `UnforcedLeray.Short.PartI.Sub.PartI_HF_1` (`trainJetsBoundedFixed_of`), where:
* the integrable-strain Grönwall lemma (`tame_gronwall_rpow`), all-order post-overlap `H^k` and
  `supNormD j` propagation (`overlap_sobolevSq_fixed_of_grad_rpow`,
  `overlap_supNormD_fixed_of_grad_rpow`), base age order `ℓ = 0` (`trainJetsBoundedFixed_zero_of_overlap`),
  and the advection age-step (`trainVelAgeStepAdvFixed_proof : TrainVelAgeStepAdvFixed`) are proved
  unconditionally;
* the remaining inputs are `OverlapMeanDuhamelSplit` (`PartI:T15/1`, completing `TrainOverlap`) and
  `TrainVelAgeStepPressFixed` (`PartI:HF/1/1`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Fixed-parameter all-order boundedness of mixed age/spatial jets of `tr.v` for `s > 0`
(`trainJetsBoundedFixed`, Task `PartI:HF/1`)**:
source lines 427–435, 326–359, 318–322, 255–258 of
`the November 2 reference manuscript`. -/
theorem trainJetsBoundedFixed : UnforcedLeray.Short.PartI.TrainJetsBoundedFixed :=
  trainJetsBoundedFixed_of overlap_mean_duhamel_split trainVelAgeStepPressFixed

end UnforcedLeray.Short.PartI

