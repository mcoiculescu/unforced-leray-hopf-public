import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.S0Weak
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.ResponseWeak

/-!
# Part III-a, `PartIII-a:T21/3/2`: `UnitHeatWeakActual` from its two conjuncts

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Assembles `unitHeatS0Weak` (`PartIII-a:T21/3/2/1`) and `unitHeatResponseWeak`
(`PartIII-a:T21/3/2/2`) into `unitHeatWeakActual` via `unitHeatWeakActual_of`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.IIIa.Exist

theorem unitHeatWeakActual : UnforcedLeray.Short.IIIa.Exist.UnitHeatWeakActual :=
  unitHeatWeakActual_of unitHeatS0Weak unitHeatResponseWeak

end UnforcedLeray.Short.IIIa.Exist
