import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_4.Inlet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_4.RawChart
import UnforcedLeray.Short.PartIIIa.Compose

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.NearInst

/-- **`PartIII-b:C/near/4`** (source 2716, 2775-2777, 2706-2713): the split multiplier bound,
from the stress coefficients of `IIIa` and the measurability of the inlet and raw chart
coefficients (`PartIII-b:C/near/4/1`, `PartIII-b:C/near/4/2`). -/
theorem splitMultBound_of (hSC : UnforcedLeray.Short.IIIa.StressCoefficients) : SplitMultBound :=
  splitMultBound_of_sub hSC inletChartMeasurable rawChartMeasurable_of

end UnforcedLeray.Short.PartIIIb.NearInst
