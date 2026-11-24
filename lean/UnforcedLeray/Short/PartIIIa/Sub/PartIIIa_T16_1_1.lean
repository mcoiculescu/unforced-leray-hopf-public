import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L1_Smooth
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L2_JointMeas
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L3_FMeas
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L4_FDerivApplyShift
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L5_FDerivBound
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L6_WEqIntegral
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1.L7_MajIntegrable

/-!
# `PartIII-a:T16/1/1` : `SepWDiffUnder` (assembly)

Source `the November 2 reference manuscript` lines 3597-3623 (`K_t`, `sep:kernel`,
`sep:resolvent`, the radial gap).

The reduction `sepWDiffUnder_of` (six analytic leaves) is proved in
`Sub/PartIII-a_T16_1_1/Defs.lean`.  The leaves are proved in the files
`Sub/PartIII-a_T16_1_1/L1_Smooth.lean` (`heatLerayKSmoothAll`), `L2_JointMeas.lean`
(`heatLerayKJointMeas`), `L3_FMeas.lean` (`sepDiffFMeas`), `L4_FDerivApplyShift.lean`
(`fDerivApplyShiftBound`, used by L5), `L5_FDerivBound.lean` (`sepDiffFDerivBound`),
`L6_WEqIntegral.lean` (`sepDiffWEqIntegral`) and `L7_MajIntegrable.lean` (`sepDiffMajIntegrable`);
the task `PartIII-a:T16/1/1` adds their imports here and the theorem
`sepWDiffUnder_proved : SepWDiffUnder := sepWDiffUnder_of heatLerayKSmoothAll sepDiffFMeas
sepDiffFDerivBound sepDiffWEqIntegral sepDiffMajIntegrable`.

The earlier split on finiteness of the order-`0` majorant (`SepWDiffFin`/`SepWDiffInf`) is
retired: the infinite case (`D^jW_μ = 0` when the majorant is infinite) is false (an isotropic
part `aI` of `T` with a non-integrable `a` makes the majorant infinite while contributing
`∑_k ∂_kK_{ik} = 0` to the signed integrand), and the finiteness of the order-`0` majorant is now
a hypothesis of `SepWDiffUnder` and `SepWDominated`, supplied a.e. by `sep:young` at order `0`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem sepWDiffUnder_proved : SepWDiffUnder :=
  sepWDiffUnder_of heatLerayKSmoothAll sepDiffFMeas sepDiffFDerivBound sepDiffWEqIntegral
    sepDiffMajIntegrable

end UnforcedLeray.Short.IIIa
