import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.PsiJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainVelSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.FixedBandJets

/-!
# Part II-b, task `PartII-b:G4/3/6/2` (`RawJetRaised`): assembly from the leaves

Source of record: `the November 2 reference manuscript` (SP) 2419-2423 and
2412-2423 (`H = (1-K)ψ`), `sct:train` 261-291, `sct:transverse` 463-467.

Composition: `rawJetRaised_of_leaves` (Sub `PartII-b_G4_3_6_2`) applied to the chart bridge
`raisedChartBridge_proof` and the stream jets `RawPsiJets`, where
`RawPsiJets = rawPsiJets_of (rawPsiTailJets_of hT) (rawVelJets_of ...) trainVelSmooth_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- `RawJetRaised` from the tail and fixed-band hypotheses of Part I (SP 2412-2423, 2419-2423). -/
theorem rawJetRaised_of (hT : UnforcedLeray.Short.PartI.TrainTransverseTails)
    (hF : UnforcedLeray.Short.PartI.TrainFixedBand) :
    UnforcedLeray.Short.IIb.RawJetRaised :=
  rawJetRaised_of_leaves raisedChartBridge_proof
    (rawPsiJets_of (rawPsiTailJets_of hT)
      (rawVelJets_of (rawVelTailJets_of hT)
        (rawVelBandJets_of trainVelSmooth_proof vcSmooth_proof vcJetSup_proof
          (fixedBandJets_of hF)))
      trainVelSmooth_proof)

end UnforcedLeray.Short.IIb

end
