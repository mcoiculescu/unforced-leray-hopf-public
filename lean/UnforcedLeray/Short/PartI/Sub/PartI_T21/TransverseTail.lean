import UnforcedLeray.Short.PartI.Sub.PartI_T21_1
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.NonzeroModeTail
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.ZeroModeTail
import UnforcedLeray.Short.PartI.Sub.PartI_T21_1.PressureTail

/-!
# `PartI:T21/1` (`Sub/PartI_T21/TransverseTail.lean`): Transverse tail for `(ψ, v, p)`

Source of record: `the November 2 reference manuscript`, lines 499-526
(old 493-515), in the proof of Lemma `sct:heat`.

Proves `trainStreamVelocityPressureTransverseTail_proof` by assembling:
1. `trainNonzeroModeStreamVelTail_proof` (`PartI:T21/1/1`, `NonzeroModeTail.lean`),
2. `trainZeroModeStreamVelTail_proof` (`PartI:T21/1/2`, `ZeroModeTail.lean`),
3. `trainPressureTransverseTail_proof` (`PartI:T21/1/3`, `PressureTail.lean`),
via `trainStreamVelocityPressureTransverseTail_of` (`PartI_T21_1.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Transverse tail for stream, velocity, and pressure (`PartI:T21/1`, source lines 499-526)**:
unconditionally proves `TrainStreamVelocityPressureTransverseTail` from `hOv : TrainOverlap`
and `hVort : TrainVorticityGaussianTail`. Composed by `PartI:T21`. -/
theorem trainStreamVelocityPressureTransverseTail_proof (hOv : TrainOverlap) (hVort : TrainVorticityGaussianTail) : TrainStreamVelocityPressureTransverseTail := by
  have hFluct := trainNonzeroModeStreamVelTail_proof hOv hVort
  have hZero := trainZeroModeStreamVelTail_proof hOv hVort
  have hPress := trainPressureTransverseTail_proof hOv hVort hFluct hZero
  exact trainStreamVelocityPressureTransverseTail_of hFluct hZero hPress hOv hVort

namespace PartI_T21

theorem trainStreamVelocityPressureTransverseTail_proof
    (hOv : TrainOverlap) (hVort : TrainVorticityGaussianTail) :
    TrainStreamVelocityPressureTransverseTail :=
  UnforcedLeray.Short.PartI.trainStreamVelocityPressureTransverseTail_proof hOv hVort

end PartI_T21

end UnforcedLeray.Short.PartI
