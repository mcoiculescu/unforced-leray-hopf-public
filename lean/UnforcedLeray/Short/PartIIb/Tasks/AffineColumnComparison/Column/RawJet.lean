import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Velocity
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Raised

/-!
# Part II-b, task `PartII-b:G4/3/6`: `RawJetBound` from the Part I hypotheses

Source of record: `the November 2 reference manuscript` (SP) 2419-2423.
The velocity jets (`rawJetVelocity_of`, task G4/3/6/1) and the raised-stream jets
(`rawJetRaised_of`, task G4/3/6/2) are merged by `rawJetBound_of_parts` (Sub `PartII-b_G4_3_6`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- `RawJetBound` from the tail and fixed-band hypotheses of Part I (SP 2419-2423). -/
theorem rawJetBound_of (hT : UnforcedLeray.Short.PartI.TrainTransverseTails)
    (hF : UnforcedLeray.Short.PartI.TrainFixedBand) : UnforcedLeray.Short.IIb.RawJetBound :=
  rawJetBound_of_parts (rawJetVelocity_of hT hF) (rawJetRaised_of hT hF)

end UnforcedLeray.Short.IIb

end
