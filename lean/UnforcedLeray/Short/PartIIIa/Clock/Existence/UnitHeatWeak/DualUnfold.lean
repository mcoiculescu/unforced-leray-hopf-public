import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.DualSplit

/-!
# Part III-a, `PartIII-a:T21/3/2/2/2/1`: the tested response is the first row of `-e^{θΔ} div T_F`

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Proves `UnitHeatDualUnfold` (`DualSplit.lean`): on the cell, `vortFn` of the physical response
`S θ F` agrees a.e. with the first component of `negativeHeatDiv θ (xFluxPeriodicTensor F)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem unitHeatDualUnfold : UnforcedLeray.Short.IIIa.Exist.UnitHeatDualUnfold := by
  intro c m _ hc1 hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro F ψ hψ θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ ≤ 1 := hθ.2
  have hc : 0 < c := Fact.out
  have hval := actualWeightedHeatResponse_value (c := c) (m := m) hm hθ0 hθ1 F
  have hae : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S θ F) x =
        (negativeHeatDiv θ (xFluxPeriodicTensor hc F) x).1 := by
    have h1 := (memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ0 hθ1 F).coeFn_toLp
    have h2 := (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le h1
    filter_upwards [h2] with x hx
    change ((actualWeightedHeatResponse (c := c) (m := m) (hm := hm) θ F :
      UnforcedLeray.B0579.X c m)) x = _
    rw [hval]
    exact hx
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]
