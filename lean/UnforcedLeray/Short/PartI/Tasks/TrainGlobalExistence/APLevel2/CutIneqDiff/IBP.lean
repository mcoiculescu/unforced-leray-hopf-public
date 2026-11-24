import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP.TimeDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP.FrozenAlg
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP.FrozenTransport
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP.FrozenViscous

/-!
# Part I, `PartI:T04/9/1/2/2/2`: `APL2IBP` from four leaves (source lines 285-288)

Assembles `aPL2IBP_of` (Sub/PartI_T04_9_1_2_2_2.lean) with the four leaf proofs
`aPL2TimeDerivQE`, `aPL2FrozenAlg`, `aPL2FrozenTransport`, `aPL2FrozenViscous`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem aPL2IBP : APL2IBP :=
  aPL2IBP_of aPL2TimeDerivQE aPL2FrozenAlg aPL2FrozenTransport aPL2FrozenViscous

end UnforcedLeray.Short.PartI
