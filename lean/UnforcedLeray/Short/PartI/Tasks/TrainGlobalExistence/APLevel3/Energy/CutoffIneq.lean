import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.ClassCommIntegrable
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.ClassVortWordCont
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.ClassVortWordEq
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.ClassVortWordSmooth
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CommWord2Bound
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CommWord2Expand
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CutoffAdvJet
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CutoffAdvTopL2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CutoffJetHasDerivOn
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CutoffViscousJet
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CutoffViscousL2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.SliceWordTimeCommOn
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.WordSqJetCompare
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.WordSqSucc
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CellIntegrable
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CurlBound
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.Measurable
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.CutoffJetContinuous

/-!
# Part I, `PartI:T04/10/1/2/1/org`: assembly of `APCutoffIneq`

Source of record: `the November 2 reference manuscript`, lines 285-288.
Assembly only: `apCutoffIneq_of` (Sub/PartI_T04_10_1_2_1.lean) applied to the proved leaves.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`APCutoffIneq`** (lines 285-288): the cutoff inequality, assembled from the proved leaves. -/
theorem apCutoffIneq_proof : APCutoffIneq :=
  apCutoffIneq_of
    (cutoffWordDeriv_of classVortWordSmooth_proof classVortWordEq_proof
      cutoffJetHasDerivOn_proof cutoffViscousJet_proof cutoffAdvJet_proof
      commWord2Bound_proof classCommIntegrable_proof wordSqJetCompare_proof
      cellVortJetIntegrable_proof curlJetBound_proof)
    (cutoffWordCont_of cutoffJetContinuous_proof classVortWordCont_proof)
    wordSqJetCompare_proof
    cellVortJetIntegrable_proof
    cutoffVortJetMeasurable_proof

end UnforcedLeray.Short.PartI
