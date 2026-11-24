import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TrainBdd
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointWeakExists
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointSmoothing.JetsBdd

/-!
# Part III-a, `PartIII-a:T21/2/7`: existence and smoothing of the reverse-time adjoint flow

Source of record: `the November 2 reference manuscript` (SP), lines 3060,
2819-2836, 270-288.

Assembles `AdjointExists m` via `adjointExistsBUC_of_regular` from:
- `ladTrainBddAll` (`Sub/T21_2_3/LinAdjDuality/TrainBdd.lean`),
- `trainJetsBddAll` (`Clock/WeakSmoothing/AdjointSmoothing/JetsBdd.lean`),
- `adjointWeakExistsBUC` (`Clock/WeakSmoothing/AdjointWeakExists.lean`),
- `adjointSmoothing` (`Clock/WeakSmoothing/AdjointSmoothing.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem adjointExists (m : ℝ) (hm : 8 < m) (hW : TrainWeightedJetPoly) : AdjointExists m :=
  adjointExistsBUC_of_regular m (ladTrainBddAll m hW) (trainJetsBddAll m hW)
    (adjointWeakExistsBUC m hm hW) (adjointSmoothing m hm)

end UnforcedLeray.Short.IIIa
