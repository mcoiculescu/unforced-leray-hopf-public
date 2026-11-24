import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_12
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.DriftPairIdent
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncDrift.TruncDriftBMem

/-!
# `truncDrift`: the weak drift of `Φₙ` lies in `Y_2` (source 1351-1362, 1470-1480)

Target: `truncDrift : TruncDrift`, obtained from `truncDrift_of` applied to the pairing identity
`driftPairIdent` and the membership `driftBMem`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `𝒯Φₙ ∈ Y_2` weakly (source 1351-1362, 1470-1480). -/
theorem truncDrift : TruncDrift :=
  truncDrift_of driftPairIdent driftBMemFix

end UnforcedLeray.Short.PartIIIb.Concrete
