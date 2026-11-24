import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.DualSplit
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.FluxHeatCLM

/-!
# Part III-a, `PartIII-a:T21/3/2/2/2/3`: the flux pairing is unchanged by periodic representatives

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Proves `FluxPairPeriodicRep` (`DualSplit.lean`): `F̃ᵢ = Fᵢ` a.e. on the cell, so the periodic
columns give the same flux pairing `fluxPair`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem fluxPairPeriodicRep : UnforcedLeray.Short.IIIa.Exist.FluxPairPeriodicRep := by
  intro c m _ hm F φ
  have hc : 0 < c := Fact.out
  have hcell : UnforcedLeray.B0579.cell c = UnforcedLeray.Cyl.cell c := by
    simp only [UnforcedLeray.B0579.cell, UnforcedLeray.Cyl.cell, neg_div]
  have h0 := xColumnPeriodicRep_ae_eq hc (F 0)
  have h1 := xColumnPeriodicRep_ae_eq hc (F 1)
  unfold fluxPair
  rw [hcell]
  refine integral_congr_ae ?_
  filter_upwards [h0, h1] with x hx0 hx1
  rw [hx0, hx1]
  rfl

end UnforcedLeray.Short.IIIa.Exist
