import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Of
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont.Age
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.TrainV
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Equation
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.BasicReg
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.HigherReg
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Deriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.ChiDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.DiffusionIBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.TransportIBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1.Remainder
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TrainBdd
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# Part III-a, `PartIII-a:T21/2/2/3`: `AdjointE1Ineq` from the leaves

Source of record: `the November 2 reference manuscript` lines 3060-3071
(`E_1' + β_min E_2 ≤ C_b(E_1 + E_0)`), 3077-3080 (`β_min = ν a_t`).
The statement is discharged by the conditional assembly `AdjE1.adjointE1Ineq_of`
(`Sub/T21_2_2/E1/Of.lean`) applied to the compiled leaves, the age map `adjAgeMap`, and
`ladTrainBddAll m hJ` for the train-bound hypothesis.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- The adjoint `E_1` inequality `E_1' + β_min E_2 ≤ C_b (E_1 + E_0)` (SP lines 3060-3071),
assembled from the leaves of the `E1` area. -/
theorem adjointE1Ineq (m : ℝ) (hm : 8 < m) (hW : PeriodicWeightLogBounds)
    (hT : RescaledTrainBounds m) (hL : AdjointLocalizedBound m) (hJ : TrainWeightedJetPoly) :
    AdjointE1Ineq m :=
  AdjE1.adjointE1Ineq_of m hT adjAgeMap (ladTrainBddAll m hJ) AdjE1.movingTrainVReg
    (AdjE1.movAdjEquation m hm) (AdjE1.movAdjBasicReg m hm) (AdjE1.movAdjHigherReg m hm)
    (AdjE1.e1MovingDeriv m hm) (AdjE1.adjChiDerivBound m hm hL)
    (AdjE1.e1RemainderBound m hm hW (AdjE1.e1DiffusionIBP m hm hW) (AdjE1.e1TransportIBP m hm hW))
    (by linarith)

end UnforcedLeray.Short.IIIa
