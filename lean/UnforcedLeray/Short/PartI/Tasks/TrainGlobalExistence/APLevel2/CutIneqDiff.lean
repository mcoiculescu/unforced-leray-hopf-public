import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.RegCopy
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.HasDerivUnder
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.TriBound
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.StripBound

/-!
# Part I, `PartI:T04/9/1/2/2`: `apL2Diff` (source lines 285-288)

Assembles `APL2Diff` from `apRReg` (the regularity proof of CutIneqReg.lean, copied into
`CutIneqDiff/RegCopy.lean` with the prefix `apL2` renamed to `apR`, because CutIneqReg.lean defines
`apL2W` with a different signature from `Sub/PartI_T04_9_1_2_2.lean`), the derivative leaf
`aPL2HasDerivUnder` with the integration-by-parts leaf `aPL2IBP` (through `apL2HasDeriv_of`),
the trilinear bound `aPL2TriBound` and the strip bound `aPL2StripBound`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem apL2Diff : APL2Diff :=
  apL2Diff_of apRReg (apL2HasDeriv_of aPL2HasDerivUnder aPL2IBP) aPL2TriBound aPL2StripBound

end UnforcedLeray.Short.PartI
