import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.BSRep.Final
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.TrainVort
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.LadGrad
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.DecayOfGrad
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.CirculationBdd
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TrainJets.KcBound

/-!
# `PartIII-a:T21/2/7/2/1/1/2/10`: `TjTrainBSRep m`

Composition of the proved train leaves (`tjTrainVort`, `tjLadGrad`, `tjDecayOfGrad`,
`tjCirculationBdd`, `tjKcBound`) with `tjTrainBSRep_of_trainLeaves`.
Source: `the November 2 reference manuscript` lines 261-266, 270-288, 2081-2084.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **`TjTrainBSRep m`**: the Biot-Savart law of the train (SP 261-266, 270-288, 2081-2084). -/
theorem tjTrainBSRep (m : ℝ) (hm : 8 < m) : TjTrainBSRep m :=
  tjTrainBSRep_of_trainLeaves m hm tjTrainVort (tjLadGrad m hm) tjDecayOfGrad
    tjCirculationBdd tjKcBound

end UnforcedLeray.Short.IIIa

#print axioms UnforcedLeray.Short.IIIa.tjTrainBSRep
