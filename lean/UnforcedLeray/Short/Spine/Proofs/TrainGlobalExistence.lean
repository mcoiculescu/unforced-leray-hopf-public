import UnforcedLeray.Short.Spine.Sub.SP_TRAIN
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistenceProof

/-!
# Spine: global existence of the train (task `Spine:SP-TRAIN`, attempt 1)

Source of record: `the November 2 reference manuscript`, lines 261-288.
The statement is that of `Short.PartI.TrainGlobalExistence` (task `PartI:T04`). The proof is the
Part I area's unconditional result `Short.PartI.trainGlobalExistence_proof`, passed through the
Spine conditional `Spine.trainGlobalExistence_of`. The named hypotheses `B0141.*` are not used.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Spine

/-- Global existence of the train in the BUC class (source lines 261-288). -/
theorem trainGlobalExistence : UnforcedLeray.Short.PartI.TrainGlobalExistence :=
  trainGlobalExistence_of UnforcedLeray.Short.PartI.trainGlobalExistence_proof

end UnforcedLeray.Short.Spine

end
