import UnforcedLeray.Short.PartI.Sub.PartI_T20_1
import UnforcedLeray.Short.PartI.Sub.PartI_T20_1.PressureStep

/-!
# `PartI:T20/1` (`Tasks/TrainVorticityTail/AgeDeriv.lean`): Age derivatives of the vorticity Gaussian tail

Source of record: `the November 2 reference manuscript`, lines 483-526
("The equations now give the age derivatives by finite induction").

All proved age-derivative induction infrastructure for vorticity and velocity—including:
* jointly smooth scalar calculus (`SmR`, `DxR`, `DtR`, `LapR`), commutation of `iteratedDeriv ℓ`
  with `Cyl.partialQ`, `Cyl.partialEta`, and `ν * Train.lapS`, and `ageJet` linearity;
* spacetime Leibniz bounds for scalar products (`PartI_T20.norm_ageJet_mul_le`), nonlinear
  advection (`PartI_T20_1.norm_ageJet_advection_le`), and pressure Poisson source
  (`PartI_T20_1.norm_ageJet_poissonSource_le`);
* iterated age-derivative vorticity equation (`PartI_T20.ageJet_succ_curl_eq`) and inductive step
  `trainVorticityGaussianTailAt_succ` (`Sub/PartI_T20_1/Base.lean`);
* iterated age-derivative momentum step (`PartI_T20_1.trainVelocityAgeJetSupBoundAt_succ`),
  simultaneous strong induction (`PartI_T20_1.trainVorticityAndVelocityAgeJet_all`), and
  conditional assembly `trainVorticityAgeDerivFromZero_of_pressure : TrainPressureAgeJetSupStep → TrainVorticityAgeDerivFromZero`
  (`Sub/PartI_T20_1.lean`)—is exported via `UnforcedLeray.Short.PartI.Sub.PartI_T20_1`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **All-age-order vorticity Gaussian tail from the age-zero spatial tail (`PartI:T20/1`)**:
source lines 523-526 (and 483-497) of `the November 2 reference manuscript`. -/
theorem trainVorticityAgeDerivFromZero_proof : TrainVorticityAgeDerivFromZero :=
  trainVorticityAgeDerivFromZero_of_pressure trainPressureAgeJetSupStep_proof

end UnforcedLeray.Short.PartI
