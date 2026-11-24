import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartStressIBP.ChartSliceIBP

/-!
# `ChartStressIBP` (task `PartIII-b:C/near/pins/4/2`)

Source `the November 2 reference manuscript` 1660-1665 (`⟨div T, Φ⟩ = -⟨T, ∇Φ⟩`).

`chartSliceIBP : ChartSliceIBP` (the slice integration by parts, in `ChartStressIBP/ChartSliceIBP.lean`)
is assembled into `ChartStressIBP` by `chartStressIBP_of` (phase average of the slice identity).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- **Integration by parts on the phase cell**: `ChartStressIBP` holds, via the slice identity. -/
theorem chartStressIBP : ChartStressIBP :=
  chartStressIBP_of chartSliceIBP

end UnforcedLeray.Short.PartIIIb.NearInst
