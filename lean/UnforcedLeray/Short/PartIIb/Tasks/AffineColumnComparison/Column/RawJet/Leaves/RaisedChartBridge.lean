import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge.StreamEq
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge.Formula
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge.JetFirst
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge.JetMixed
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge.JetSecond
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.RaisedChartBridge.Symm

/-!


Applies `raisedChartBridge_of` to the six leaf proofs.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem raisedChartBridge_proof : UnforcedLeray.Short.IIb.RaisedChartBridge :=
  raisedChartBridge_of raisedStreamEq_proof raisedFormula_proof raisedJetFirst_proof
    raisedJetMixed_proof raisedJetSecond_proof raisedSymm_proof

end UnforcedLeray.Short.IIb
