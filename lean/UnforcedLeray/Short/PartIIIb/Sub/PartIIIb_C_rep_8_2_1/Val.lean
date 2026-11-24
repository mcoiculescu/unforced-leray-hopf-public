import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1.Bridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1.Raised
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_1.Smooth

/-!
# `RingChartRawVal` (`PartIII-b:C/rep/8/2/1/1`)

Source `the November 2 reference manuscript`
lines 2073-2077 (`U_raw = √s[v₁e_r + (v₂ + εH)e_z]`, `H = (1-K)ψ`), 5460-5465 (exact ring-chart
rules, `U_raw = √s(v + εHe_z)` with `H` bounded by the weighted train jets).

Assembly of the three pieces of `Sub/PartIII-b_C_rep_8_2_1_1.lean`: the ring-chart bridge at
azimuth `0` (`Bridge.lean`), the raised-stream bound (`Raised.lean`), and the joint smoothness of
the decaying stream in `(σ,q,η)` (`Smooth.lean`, from the `ReturnLevel` field
`train_stream_smooth`: the actual train is the BUC train, smooth for `s > 0`, source 270-288, 397,
2040-2049).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(i) of the exact ring-chart rules**: `U_raw - √s v = √s·ε·H·e_z` with `|H| ≤ 3𝔴₃`
(source 2073-2077, 5460-5465). -/
theorem ringChartRawVal : RingChartRawVal :=
  ringChartRawVal_of ringChartBridge raisedStreamBound trainStreamSmooth

end UnforcedLeray.Short.PartIIIb.Concrete

end
