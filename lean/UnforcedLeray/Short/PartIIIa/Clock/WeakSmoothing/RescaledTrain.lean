import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.CenteredLatticeWeighted
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.CurlJetBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.DatumCurlLattice
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.DatumCurlScale
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.DatumCurlWeighted
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.ExpPolyAbsorb
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.FluctJetWeighted
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.GaussVortMoving
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MeanJetWeighted
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MeanStreamJetBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MeanVecFormula
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MovingTrainEJet
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MovingTrainVJet
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.RescaledVelPhys
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.RescaledVortPhys
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.TrainWeightedJetPoly
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.VcWeightedJet
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.VortErrMoving

/-!
# Part III-a, `PartIII-a:T21/2/6`: `rescaledTrainBounds`

Source of record: `the November 2 reference manuscript` (SP) lines 3050-3051,
2866-2873, 290-336, 397-404, 437-459. The proof is the assembly `rescaledTrainBoundsBUC_of` of the
eighteen leaves of `Sub/T21_2_6/`, applied to the Part I hypotheses `TrainComparison`,
`TrainFluctuationDecay`, `TrainMeanExpansion`, `TrainMeanEquations`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **The rescaled BUC train is uniformly bounded** (SP 3050-3051): for the Gallay-Slijepcevic
train of the source, `RescaledTrainBoundsBUC m` holds, from the Part I comparison, fluctuation,
mean-expansion and mean-equation hypotheses. -/
theorem rescaledTrainBounds (m : ℝ) (hcmp : UnforcedLeray.Short.PartI.TrainComparison)
    (hfl : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hme : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hmeq : UnforcedLeray.Short.PartI.TrainMeanEquations) :
    RescaledTrainBoundsBUC m :=
  rescaledTrainBoundsBUC_of m movingTrainVJet movingTrainEJet
    (rescaledVelPhys_of hcmp vcWeightedJet)
    (rescaledVortPhys_of m
      (gaussVortMoving_of datumCurlScale
        (datumCurlWeighted_of datumCurlLattice centeredLatticeWeighted))
      (vortErrMoving_of hcmp
        (trainWeightedJetPoly_of (fluctJetWeighted_of hfl)
          (meanJetWeighted_of (meanVecFormula_of hmeq) (meanStreamJetBound_of hme hmeq))
          vcWeightedJet)
        vcWeightedJet curlJetBound expPolyAbsorb))

end UnforcedLeray.Short.IIIa
