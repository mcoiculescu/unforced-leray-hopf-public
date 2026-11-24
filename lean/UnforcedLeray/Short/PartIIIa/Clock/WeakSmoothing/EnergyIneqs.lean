import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.Cont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E0
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2.E1

/-!
# Part III-a, `PartIII-a:T21/2/2`: the adjoint energy inequalities (unconditional)

Source of record: `the November 2 reference manuscript` lines 3060-3071.

The conditional assembly `adjointEnergyIneqs_of` (in `Sub/PartIIIa_T21_2_2.lean`) combines the
continuity leaf `adjointEnergyCont` (`Sub/T21_2_2/Cont.lean`, task `T21/2/2/1`), the `E_0` leaf
`adjointE0Ineq` (`Sub/T21_2_2/E0.lean`, task `T21/2/2/2`) and the `E_1` leaf `adjointE1Ineq`
(`Sub/T21_2_2/E1.lean`, task `T21/2/2/3`). Here the three leaves are applied with
`hm hW hT hL hJ`; the signature of `adjointEnergyIneqs` is unchanged.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem adjointEnergyIneqs (m : ℝ) (hm : 8 < m) (hW : PeriodicWeightLogBounds)
    (hT : RescaledTrainBounds m) (hL : AdjointLocalizedBound m) (hJ : TrainWeightedJetPoly) :
    AdjointEnergyIneqs m :=
  adjointEnergyIneqs_of m (adjointEnergyCont m hm) (adjointE0Ineq m hm hW hT hL hJ)
    (adjointE1Ineq m hm hW hT hL hJ)

end UnforcedLeray.Short.IIIa
