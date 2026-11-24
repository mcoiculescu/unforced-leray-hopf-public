import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletLap.Gen

/-!
# Part II-b, task `PartII-b:G4/3/3` (`InletLapPtw`): the Laplacian of the affine inlet in the chart

Source of record: `the November 2 reference manuscript`, lines 1651-1658
(`A_ε = -S + ν s[(Q_ε² + ∂_η²)I - ε²E]`), 2367-2369 (`L_ε = Δ - 2ε(K+1)∂_q + ε²[(K+1)² - diag(1,0)]`).

The reduction `InletLapGen → InletLapPtw` is `inletLapPtw_of` (`Sub/PartII-b_G4_3_3.lean`).
The leaf `InletLapGen` is proved by `inletLapGen` (`InletLap/Gen.lean`, task `PartII-b:G4/3/3/1`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:G4/3/3`**: the vector Laplacian of the affine inlet in the chart
(`InletLapPtw`), from the off-axis chart identity `inletLapGen`. -/
theorem inletLapPtw : UnforcedLeray.Short.IIb.InletLapPtw :=
  inletLapPtw_of inletLapGen

end UnforcedLeray.Short.IIb
