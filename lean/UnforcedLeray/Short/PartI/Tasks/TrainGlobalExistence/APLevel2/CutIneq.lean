import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff

/-!
# Part I, `PartI:T04/9/1/2`: `apLevel2CutIneq`

Source of record: `the November 2 reference manuscript`, lines 285-288.

Assembly: `apLevel2CutIneq_of` applied to the regularity leaf `apRReg`
(`APLevel2/CutIneqDiff/RegCopy.lean`, the copy of `apL2Reg` from `APLevel2/CutIneqReg.lean`
with prefix `apR`) and the integrated differential inequality `apL2Diff`
(`APLevel2/CutIneqDiff.lean`). `CutIneqReg.lean` is not imported: it defines `apL2W` with a
different signature from `Sub/PartI_T04_9_1_2_2.lean`, which `CutIneqDiff` imports.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem apLevel2CutIneq : APLevel2CutIneq :=
  apLevel2CutIneq_of apRReg apL2Diff

end UnforcedLeray.Short.PartI
