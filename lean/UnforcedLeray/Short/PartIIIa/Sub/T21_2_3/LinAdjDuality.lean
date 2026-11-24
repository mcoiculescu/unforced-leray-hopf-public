import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDualitySub
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLip
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ProductRule
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TrainBdd
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ChiBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.Transposition
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.ForceMemX
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CommVanish
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjGradInt
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.RateBound

/-!
# `PartIII-a:T21/2/3/1` (`LinAdjDualityBUC`): the linear adjoint duality from its leaves

Composes `linAdjDualityBUC_of` (`LinAdjDualitySub.lean`) with the fourteen leaves `PartIII-a:T21/2/3/1/1`
to `/14`.  Replaces the former target `linAdjDuality`, which quantified over every `B0140.TrainSol`
and is not derivable from `B0140.IsTrain` (no global bound on the train).  Source:
`the November 2 reference manuscript` lines 3074-3075 (duality), 270-288, 2824,
2866-2873, 3052-3071, 3230-3240.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem linAdjDualityBUC (m : ℝ) (hm : 8 < m) (hW : TrainWeightedJetPoly) : LinAdjDualityBUC m :=
  linAdjDualityBUC_of m ladPairCont ladCutLimit (ladVelLip m hm) ladProductRule
    (ladTrainBddAll m hW)
    (ladRatePointwise_of m ladCutLimit (ladChiBound m hm) (ladTransposition m hm)
      (ladForceMemX m) ladRateSplit (ladCommVanish m))
    (ladRateBound m hm)

end UnforcedLeray.Short.IIIa
