import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Assembly
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.JetNorm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.WPerm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.WLeibniz
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.WLinear
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.TrainVort
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.BSRep
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.SliceNorm
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.SpatialInterp
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.DecayOfGrad
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.CirculationBdd
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.LadGrad
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.KcBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.KcDerivSpace
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.KcDerivTime
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.WPeriodic

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- `PartIII-a:T21/2/7/2/1/1/2`: `TrainSTJetsOfBUC m` from its leaves. -/
theorem trainSTJetsOfBUC (m : ℝ) (hm : 8 < m) : TrainSTJetsOfBUC m :=
  trainSTJetsOfBUC_of m hm tjJetNorm tjWPerm tjWLeibniz tjWLinear tjTrainVort tjSliceNorm
    tjSpatialInterp tjDecayOfGrad tjCirculationBdd (tjLadGrad m hm) (tjTrainBSRep m hm)
    tjKcBound tjKcDerivSpace tjKcDerivTime tjWPeriodic

end UnforcedLeray.Short.IIIa
