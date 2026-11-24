import UnforcedLeray.Short.PartI.Sub.T07
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.Agmon
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.GradInterp
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.GN

/-!
# Part I, task `PartI:T07`, target `cylinder_interpolation_uniform`

Source of record: `the November 2 reference manuscript`, lines 355-357 (conjunct 2,
the period-independent Gagliardo-Nirenberg inequality) and lines 366-374 (conjunct 1, the cylinder
interpolation inequality for the sup norm). The Prop is `CylinderInterpolationUniform = CylSupInterp ∧ CylGN`
in `Sub/T07.lean`.

Proof. The three compiled inputs are `cylAgmonL2_proof : CylAgmonL2` (`Tasks/CylinderInterpolation/Agmon`),
`cylGradInterpL2_proof : CylGradInterpL2` (`Tasks/CylinderInterpolation/GradInterp`) and
`cylGN_proof : CylGN` (`Tasks/CylinderInterpolation/GN`). Feeding them to the proved conditional
theorem `cylinder_interpolation_uniform_of` yields the target.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Target** `cylinder_interpolation_uniform` (source lines 355-357 and 366-374): both conjuncts
of the cylinder interpolation, unconditionally. -/
theorem cylinder_interpolation_uniform : UnforcedLeray.Short.PartI.CylinderInterpolationUniform :=
  cylinder_interpolation_uniform_of cylAgmonL2_proof cylGradInterpL2_proof cylGN_proof

end UnforcedLeray.Short.PartI
