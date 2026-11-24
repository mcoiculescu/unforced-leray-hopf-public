import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_Org
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.FlatAdjointWeakEq
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.GenDiffIBP
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.CoreSupport
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.FlatProjComm
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.BandCutoff

/-!
# `PartII-a:N04/3`: `AdjointResidualEq`

Source: `the November 2 reference manuscript` lines 1828-1848.
Assembles `adjointResidualEq` from `adjointResidualEq_of_core` and the six leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem adjointResidualEq : AdjointResidualEq :=
  adjointResidualEq_of_core flatAdjointWeakEq genDiffIBP
    (meridCoreTestLocalize_of meridCoreTestSupport profileBandCutoff)
    flatProjCommSMul repsVecAdjointOfWeakEqCore

end UnforcedLeray.Short.PartIIa
