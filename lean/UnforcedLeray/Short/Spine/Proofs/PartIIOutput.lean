import UnforcedLeray.Short.Spine.Sub.SP_PII
import UnforcedLeray.Short.Spine.Proofs.BallB3Output
import UnforcedLeray.Short.Spine.Proofs.BallRepairRegularity
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartIIb.Tasks.InteractionCylinder
import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization
import UnforcedLeray.Short.PartIIb.Tasks.InvariantProjections
import UnforcedLeray.Short.PartIIb.Tasks.BodySource
import UnforcedLeray.Short.PartIIb.Tasks.EarlyBound
import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy
import UnforcedLeray.Short.PartIIb.Tasks.LocalSmoothing
import UnforcedLeray.Short.PartIIb.Tasks.FlatReconstruction
import UnforcedLeray.Short.PartIIb.Tasks.FlatInverse
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication
import UnforcedLeray.Short.PartIIb.Tasks.LpFreeComparison
import UnforcedLeray.Short.PartIIb.Tasks.LocalInteractionComparison
import UnforcedLeray.Short.PartIIb.Tasks.StrongLateCoeff
import UnforcedLeray.Short.PartIIb.Tasks.TailOperatorBounds
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison
import UnforcedLeray.Short.PartIIb.Tasks.GlobalOperatorComparison
import UnforcedLeray.Short.PartIIb.Tasks.PhysicalRowReduction
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticFamily
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularityProof

/-!
# Spine, task `Spine:SP-PII` — Assembly of `PartIIOutput`

Unconditionally assembles `UnforcedLeray.Short.Spine.PartIIOutput` from the
Part II-b chain, `IIb.strongRegularity_proof`, `SPPII.ballB3Output`,
`SPPII.ballRepairRegularity`, and `PartI.trainStreamSmooth`.
-/

namespace UnforcedLeray.Short.Spine

theorem partIIOutput : UnforcedLeray.Short.Spine.PartIIOutput := by
  have hBD := IIb.blockDichotomy_of IIb.interactionCylinder_proof.1 IIb.interactionCylinder_proof.2
  have hDP := IIb.dichotomyProjections_of hBD
  have hEB := IIb.earlyBound_of_duhamel hDP IIb.bodySourceBound_proof
  have hGE := IIb.tailSourceAndGlobalEnergy_of hEB IIb.bodySourceBound_proof
  have hLS := _root_.localSmoothing_of hGE
  have hFI := IIb.flatInverse_of (IIb.flatReconstruction_of hGE hLS)
  have h19 := IIb.lpFreeComparison_of IIb.hilbertBodyComparison_proof (IIb.lpInterpolationStep_of IIb.hilbertBodyComparison_proof)
  have h20 := IIb.localInteractionComparison_of h19
  have hG2 := IIb.youngLateOperatorBounds_of IIb.strongLateCoeff_proof
  have hG5 := IIb.globalOperatorComparison_of hG2 (IIb.windowComparison_of h20 hG2) IIb.affineInletFacts_proof
  have hQ2 := IIb.quadraticFamily_of (IIb.quadBound_of IIb.affineInletFacts_proof)
  have hBR := IIb.backgroundResult_of_leaves hFI hG5 IIb.physicalRowReduction_proof hQ2 IIb.rawResidualFamily_proof
  exact SPPII.partIIOutput_of hBR IIb.strongRegularity_proof SPPII.ballB3Output SPPII.ballRepairRegularity PartI.trainStreamSmooth

end UnforcedLeray.Short.Spine
