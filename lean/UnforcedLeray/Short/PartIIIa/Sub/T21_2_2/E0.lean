import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.Age
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.MovingEq
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reynolds
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reg
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Train
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Weight
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Chi
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Reduce
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0.Estimate
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TrainBdd
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# Part III-a, `PartIII-a:T21/2/2/2`: `AdjointE0Ineq` from the leaves

Source of record: `the November 2 reference manuscript` lines 3060-3066.
The statement is discharged by the conditional assembly `E0.adjointE0Ineq_of`
(`Sub/T21_2_2/E0/Assembly.lean`) applied to the compiled leaves, the age map `adjAgeMap`,
and `ladTrainBddAll m hJ` for the train-bound hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- The adjoint `E_0` inequality `E_0' + β_min E_1 ≤ C_b E_0` (SP lines 3060-3066), assembled
from the leaves of the `E0` area. -/
theorem adjointE0Ineq (m : ℝ) (hm : 8 < m) (hW : PeriodicWeightLogBounds)
    (hT : RescaledTrainBounds m) (hL : AdjointLocalizedBound m) (hJ : TrainWeightedJetPoly) :
    AdjointE0Ineq m :=
  E0.adjointE0Ineq_of m hT adjAgeMap (ladTrainBddAll m hJ) (E0.movingAdjointEq m hm)
    (E0.adjE0Reynolds m hm) (E0.revPhiReg m hm) E0.movingTrainReg (E0.adjWeightBounds m hm hW)
    (E0.adjChiWeighted m hm hL) E0.cellRateReduce E0.cellRateEstimate

end UnforcedLeray.Short.IIIa
