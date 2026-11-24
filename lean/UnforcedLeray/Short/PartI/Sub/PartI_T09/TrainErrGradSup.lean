import UnforcedLeray.Short.PartI.Sub.PartI_T09_6
import UnforcedLeray.Short.PartI.Sub.PartI_T09_6.Bdd
import UnforcedLeray.Short.PartI.Sub.PartI_T09_6.Cont

/-!
# Part I, task `PartI:T09/6`: `TrainErrGradSup`

Source of record: `the November 2 reference manuscript`, lines 270-288 and 355.

Assembly: `TrainErrGradSup` follows from `TrainErrGradBdd` (`trainErrGradBdd_proof`, in `PartI_T09_6/Bdd.lean`)
and `TrainErrGradCont` (`trainErrGradCont_proof`, in `PartI_T09_6/Cont.lean`) via `trainErrGradSup_of`
(in `PartI_T09_6.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem trainErrGradSup_proof : TrainErrGradSup :=
  trainErrGradSup_of trainErrGradBdd_proof trainErrGradCont_proof

end UnforcedLeray.Short.PartI
