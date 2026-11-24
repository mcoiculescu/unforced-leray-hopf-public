import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_8
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.WeightNorm
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.JetLe
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.VecDiffJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.RawProfJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.ColVanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.TrainDiff
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.FlatColumnReal
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.FlatColVanish
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.InletComponentJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.VecDiffFlat
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.BEpsFlat
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.Parts.DiffRealParts

/-!
# Part II-b, task `PartII-b:G4/3/8` (`ColumnDifference`): assembly

Source of record: `the November 2 reference manuscript` (SP), lines 2360-2379.
Composes the part lemmas (`Column/Parts/*.lean`) through `columnDifference_of_parts`
(`Sub/PartII-b_G4_3_8.lean`) and `diffReal_of_parts` (`Parts/DiffRealParts.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`ColumnDifference` from `RawJetBound`** (SP 2360-2379). -/
theorem columnDifference_of (hR : UnforcedLeray.Short.IIb.RawJetBound) :
    UnforcedLeray.Short.IIb.ColumnDifference :=
  columnDifference_of_parts colWeightNorm flatColumnReal flatColVanish colVanish
    (diffReal_of_parts trainDiff (rawProfJet_of hR) inletComponentJets vecDiffFlat bEpsFlat
      jetLe vecDiffJet)

end UnforcedLeray.Short.IIb

end
