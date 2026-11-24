import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1_2
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxHeatCLM

/-!
# Part III-a, `PartIII-a:T21/3/2/1/2/2`: `UnitHeatLiftIntegrable` (lemma D)

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
The first component of the lift of `w ∈ X_{m,c}` is its periodic representative, which is
integrable on the cell by `integrable_xColumnPeriodicRep`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem unitHeatLiftIntegrable : UnforcedLeray.Short.IIIa.Exist.UnitHeatLiftIntegrable := by
  intro c m _ hm w
  have hc : 0 < c := Fact.out
  have h := integrable_xColumnPeriodicRep hc hm w
  have hleft : -(c / 2) = -c / 2 := by ring
  simpa [xColumnHeatLift, UnforcedLeray.B0579.cell, UnforcedLeray.Cyl.cell,
    UnforcedLeray.Cyl.cellμ, IntegrableOn, hleft] using h

end UnforcedLeray.Short.IIIa.Exist
