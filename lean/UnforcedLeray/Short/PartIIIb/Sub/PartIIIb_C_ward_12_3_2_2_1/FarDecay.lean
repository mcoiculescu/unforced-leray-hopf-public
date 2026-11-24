import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1.EarlyJet2

/-!
# `PartIII-b:C/ward/12/3/2/2/1/1`: `RawResidualD2FarDecay`

Source of record:
`the November 2 reference manuscript`,
lines 2542-2548 at `k = 2`, 1255-1305.

Assembles `rawResidualD2FarDecay : RawResidualD2FarDecay` from the conditional reduction
`rawResidualD2FarDecay_of : ResProfileFarJet → RawResidualD2FarDecay`
(`UnforcedLeray.Short.«PartIII-b».Sub.«PartIII-b_C_ward_12_3_2_2_1_1»`) and the proved early-age
chart jet bound `resProfileEarlyJet2 : ResProfileEarlyJet2` via `resProfileFarJet_of_earlyJet2`
(`UnforcedLeray.Short.«PartIII-b».Sub.«PartIII-b_C_ward_12_3_2_2_1_2_1».EarlyJet2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Zero-age (`0 < s ≤ s0`) order-`≤ 2` chart-jet decay of `resChartProfile p` (`s0 = 1`). -/
theorem resProfileFarJet : ResProfileFarJet :=
  resProfileFarJet_of_earlyJet2 resProfileEarlyJet2

/-- **Order-2 far-field decay of the raw ring residual** (`PartIII-b:C/ward/12/3/2/2/1/1`,
`the November 2 reference manuscript`, lines 2542-2548 at `k = 2`, 1287-1305). -/
theorem rawResidualD2FarDecay : RawResidualD2FarDecay :=
  rawResidualD2FarDecay_of resProfileFarJet

namespace Ward

export UnforcedLeray.Short.PartIIIb.Concrete (rawResidualD2FarDecay)

end Ward

end UnforcedLeray.Short.PartIIIb.Concrete
