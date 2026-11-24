import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_10
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_2_10.Shift

/-!
# `pdSourceFinite`: the period shift discharges the source finiteness

Source `the November 2 reference manuscript` 2667 (period `P = 2c/R`), 3631-3646,
5585-5589.

`PDSourceFinite` is reduced to the period-shift bound `PDShiftBound` by `pdSourceFinite_of`, and
`PDShiftBound` is proved in `Shift.lean` as `pdShiftBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Source finiteness for the pointwise domination** (source 2667, 3631-3646, 5585-5589).
Discharged by the period shift `pdShiftBound` through `pdSourceFinite_of`. -/
theorem pdSourceFinite : PDSourceFinite :=
  pdSourceFinite_of pdShiftBound

end UnforcedLeray.Short.PartIIIb.Concrete

end
