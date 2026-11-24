import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.Adjoint
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingBoundBUC
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.PairingCoV
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.MovingPhiH1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.H1BySeminorm
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.NegNormPairing
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# `PartIII-a:T21/2/3` (`AdjointPairingBound`): the adjoint pairing bound, BUC form

Composes `adjointPairingBoundBUC_of` (`Sub/T21_2_3/PairingBoundBUC.lean`) with
`linAdjDualityBUC` (`Sub/T21_2_3/LinAdjDuality.lean`, task `PartIII-a:T21/2/3/1`), `pairingCoV`,
`movingPhiH1`, `h1BySeminorm` and `negNormPairing`.  The target is the BUC form `AdjointPairingBound`
(`Clock/WeakSmoothing/Adjoint.lean`), which replaces the retired every-train target.
Source: `the November 2 reference manuscript` lines 3036-3040, 3044, 3074-3075, 270-288, 2824.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem adjointPairingBound (m : ℝ) (hm : 8 < m) (hW : TrainWeightedJetPoly) :
    AdjointPairingBound m :=
  adjointPairingBoundBUC_of m hm (linAdjDualityBUC m hm hW) pairingCoV (movingPhiH1 m)
    (h1BySeminorm m) negNormPairing

end UnforcedLeray.Short.IIIa
