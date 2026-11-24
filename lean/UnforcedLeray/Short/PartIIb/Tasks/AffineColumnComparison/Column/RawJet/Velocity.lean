import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainChartBridge
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.TrainVelSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelTail
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelBand
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VelJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.FixedBandJets

/-!
# Part II-b, task `PartII-b:G4/3/6/1`: `RawJetVelocity` from the leaves

Source of record: `the November 2 reference manuscript` (SP) 2419-2423.
Composition: `rawJetVelocity_of_leaves` applied to the chart bridge and the velocity jets
`RawVelJets = rawVelJets_of (rawVelTailJets_of hT) (rawVelBandJets_of ...)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- `RawJetVelocity` from the tail and fixed-band hypotheses of Part I (SP 2419-2423). -/
theorem rawJetVelocity_of (hT : UnforcedLeray.Short.PartI.TrainTransverseTails)
    (hF : UnforcedLeray.Short.PartI.TrainFixedBand) :
    UnforcedLeray.Short.IIb.RawJetVelocity :=
  rawJetVelocity_of_leaves (trainChartBridge_of trainVelSmooth_proof)
    (rawVelJets_of (rawVelTailJets_of hT)
      (rawVelBandJets_of trainVelSmooth_proof vcSmooth_proof vcJetSup_proof
        (fixedBandJets_of hF)))

end UnforcedLeray.Short.IIb

end
