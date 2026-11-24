import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Producer
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.NearLayer
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Assembly
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.OutPartition
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.TrainMult
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.ThinDiffMult
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.BroadMult
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.RawStream
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.RepairCoeff
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.PartialStrip
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.YoungEnd
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.OldEnd
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Exists
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RAExists
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.HEx
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EACoefBound

/-!
# `PartIII-b:C/standing`: instantiated producer of `SeqData.RepairStanding`

Source of record: `the November 2 reference manuscript` (lines 5115-5146,
5777-5833, 5835-5859, 5926-5950).

Instantiates `repairStanding_of_inputs` (`Concrete/Standing/Producer.lean`) with:
* `nearSolverC_of_layers` (`Concrete/Standing/NearLayer.lean`) composed with
  `NearInst.Delta.nearDeltaBoundC_of` (`NearInst/Delta/Assembly.lean`) and its compiled leaves;
* `nearOpsExistCC` (`PartIII-b:C/rep/5/1/1/1/2`);
* `seqWardTriple_exists` (`PartIII-b:C/ward`);
* `raBoundExists` (`PartIII-b:C/asrc/ra`);
* `eaCoefBound` (`PartIII-b:C/inst/10`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem repairStanding_concrete
    (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hCF : UnforcedLeray.Short.PartIIa.NearCompactFreeComparison)
    (hSR : UnforcedLeray.Short.IIb.StrongRegularity)
    (hK : UnforcedLeray.Short.IIIa.SepKernelBounds)
    (hY : UnforcedLeray.Short.IIIa.SepYoung)
    (hPC : UnforcedLeray.Short.IIIa.PolyCausal)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique)
    (hRE : UnforcedLeray.Short.IIIa.RawCoeffEarly)
    (hRL : UnforcedLeray.Short.IIIa.RawCoeffLate)
    (hIn : UnforcedLeray.Short.IIIa.InletCoeffBounds)
    (hRT : UnforcedLeray.Short.IIIa.RawTransverseTail)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (Pl : UnforcedLeray.Blueprint.Planar.PlanarData)
    (hP : UnforcedLeray.Blueprint.Planar.IsPlanarReference Pl)
    (hω : Pl.eigenvalue.im ≠ 0)
    (σ₀ : ℝ) (hσ₀ : 0 < σ₀) (hσ₁ : σ₀ < 1 / 4)
    (mZ : ℝ) (hmZ : 3 / 2 < mZ)
    (dm dp : ℝ) (hdm : 0 < dm) :
    ∃ Kint : ℕ, ∀ D : SeqData, D.Pl = Pl → D.σ₀ = σ₀ → D.K.mZ = mZ →
      D.StandingChoices Kint dm → D.StandingBridge dm dp → D.RepairStanding dm dp := by
  have hDelta : NearInst.NearDeltaBoundC :=
    NearInst.Delta.nearDeltaBoundC_of
      NearInst.Delta.outPartitionSum
      NearInst.Delta.trainMultRestr
      NearInst.Delta.thinDiffMult
      NearInst.Delta.broadMult
      NearInst.Delta.rawStreamCompletion
      NearInst.Delta.repairCoeffBound
      (NearInst.Delta.flatFreeGainBound_of hU)
      (NearInst.Delta.Target.compactWindowBlock_of hCF hN hU)
      (NearInst.Delta.partialStripBlock_of hK hY hU)
      (NearInst.Delta.youngEndResponse_of hN hK hY hU)
      (NearInst.Delta.oldEndResponse_of hN hU)
      hRE hRL hIn hRT
      (NearInst.flatTrainMultBound_of hF hM hE)
      (nearMaskedFreeBoundC_of_leaves hN hK hY)
  have hNS : NearInst.NearSolverC :=
    nearSolverC_of_layers hDelta hN hK hY hPC hU hF hM hE
  have hW : SeqWardTripleSupply :=
    fun D dm' dp' hq hω' hσ0' hσ1' hm0 h2m hC0 hmZ' hχy hact =>
      seqWardTriple_exists (dm := dm') (dp := dp') D hq hω' hσ0' hσ1' hm0 h2m hC0 hmZ' hχy hact
  exact repairStanding_of_inputs
    hNS
    UnforcedLeray.Short.PartIIIb.nearOpsExistCC
    hW
    raBoundExists
    hN
    hSR
    eaCoefBound
    Pl hP hω σ₀ hσ₀ hσ₁ mZ hmZ dm dp hdm

end UnforcedLeray.Short.PartIIIb.Concrete
end
