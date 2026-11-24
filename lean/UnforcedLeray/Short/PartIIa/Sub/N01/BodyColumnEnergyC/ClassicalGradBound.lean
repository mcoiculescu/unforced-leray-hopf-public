import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_3_3_2_1
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HeatIntGradSlice
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HardyGradKernel
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.HSqNormEq
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.ClassicalGradBound.GradAgeSliceBound

/-!
# `PartII-a:N01/9/1/3/3/2/1`: `classicalGradBound`

Assembly of the four lemma theorems (`heatIntGradSlice`, `hardyGradKernel`, `hSqNormEq`,
`gradAgeSliceBound`) into `classicalGradBound_of`.
-/

set_option autoImplicit false

theorem classicalGradBound : UnforcedLeray.Short.PartIIa.N01.ClassicalGradBound :=
  UnforcedLeray.Short.PartIIa.N01.classicalGradBound_of heatIntGradSlice
    UnforcedLeray.Short.PartIIa.N01.hardyGradKernel
    UnforcedLeray.Short.PartIIa.N01.hSqNormEq
    UnforcedLeray.Short.PartIIa.N01.gradAgeSliceBound
