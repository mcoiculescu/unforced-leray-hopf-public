import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.WeightNorm
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.QPeriodic
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.Meas
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletJetDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.JetLe
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.VecDiffJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.BEpsJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.RawProfJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.ColVanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.EnvelopeParts

/-!
# Part II-b, task `PartII-b:G4/3/7` (`ColumnMem`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 2347-2348, 2385.
Assembles `ColumnMem` from the ten part lemmas of the column decomposition.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`ColumnMem` from the raw jet bound** (SP 2347-2348, 2385). -/
theorem columnMem_of (hR : UnforcedLeray.Short.IIb.RawJetBound) :
    UnforcedLeray.Short.IIb.ColumnMem :=
  columnMem_of_parts colWeightNorm colQPeriodic colAEMeas
    (colEnvelope_of_parts (rawProfJet_of hR) inletJetDecay jetLe vecDiffJet bEpsJet colVanish)

end UnforcedLeray.Short.IIb

end
