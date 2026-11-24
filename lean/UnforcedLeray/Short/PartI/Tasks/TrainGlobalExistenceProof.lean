import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Short.PartI.Sub.T04.Compose
import UnforcedLeray.Short.PartI.Sub.T04.APriori
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.MildConcat
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.H3NormOfRep
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.JetL2FromPersistent
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.TrainOnUnique
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APMaxPrinciple
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APElliptic
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3

/-! Assembly of `PartI:T04` (unconditional). Source of record:
`the November 2 reference manuscript`, lines 261-288. -/

namespace UnforcedLeray.Short.PartI

/-- Global existence of the train in the BUC class (`PartI:T04`, lines 261-288). -/
theorem trainGlobalExistence_proof : TrainGlobalExistence :=
  trainGlobalExistence_of mildConcat h3NormOfRep jetL2FromPersistent trainOnUnique
    (classicalH3APriori_of apEnergy apEnstrophy apMaxPrinciple apElliptic apLevel2 apLevel3)

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.trainGlobalExistence_proof
