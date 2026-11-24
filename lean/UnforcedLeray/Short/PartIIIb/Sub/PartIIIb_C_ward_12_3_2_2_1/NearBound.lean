import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2
import UnforcedLeray.Short.PartIIa.Tasks.R06AxisSmooth
import UnforcedLeray.Short.PartIIb.Tasks.RawResidualFamily.RingLiftSmoothExt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2.AxialTail

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2`: `RawResidualD2NearBound`

Source of record:
`the November 2 reference manuscript`,
lines 1270-1325, 2548-2551 at `k = 2`.

Assembles `rawResidualD2NearBound : RawResidualD2NearBound` from
`rawResidualD2NearBound_of`, `ringLiftSmoothExt_of ringAxisSmooth`, and
`rawResidualD2AxialTail`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Near-axis cylinder second-derivative bound for the raw ring residual**
(`PartIII-b:C/ward/12/3/2/2/1/2`, `the November 2 reference manuscript`, lines 1270-1325,
2548-2551). -/
theorem rawResidualD2NearBound : RawResidualD2NearBound :=
  rawResidualD2NearBound_of
    (UnforcedLeray.Short.IIb.ringLiftSmoothExt_of UnforcedLeray.Short.PartIIa.ringAxisSmooth)
    rawResidualD2AxialTail

end UnforcedLeray.Short.PartIIIb.Concrete
