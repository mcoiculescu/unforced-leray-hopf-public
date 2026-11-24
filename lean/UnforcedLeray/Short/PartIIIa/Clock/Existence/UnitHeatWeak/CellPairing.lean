import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_1

/-!
# Part III-a, `PartIII-a:T21/3/2/1/1`: the cell pairing of `S₀` (L1)

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
For `0 < θ ≤ 1` the physical `S₀ θ w` agrees with the positive-age heat image
`xColumnHeatS0Positive` (`actualWeightedHeatS0_apply_of_pos`), whose cell representative is
the first component of the Gaussian heat flow (`coeFn_xColumnHeatS0Positive`). The cell measure
dominates Lebesgue measure on the cell (`B0579.ac_cellMeasure`), so the two integrands agree
almost everywhere on the cell.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

theorem unitHeatCellPairing : UnforcedLeray.Short.IIIa.Exist.UnitHeatCellPairing := by
  intro c m _ hc1 hm
  haveI := actualVorticityCompleteSpace (c := c) (m := m) hm
  intro w ψ _hψ θ hθ
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ ≤ 1 := hθ.2
  have hc : 0 < c := Fact.out
  have hae : ∀ᵐ x ∂(volume.restrict (UnforcedLeray.B0579.cell c)),
      vortFn hm ((actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ θ w) x =
        (UnforcedLeray.B0284.heat θ (xColumnHeatLift hc w.1) x).1 := by
    have h1 := coeFn_xColumnHeatS0Positive (c := c) (m := m) (θ := θ) hc hm hθ0 hθ1 w.1
    have h2 := (UnforcedLeray.B0579.ac_cellMeasure c m).ae_le h1
    have hv : ((actualWeightedHeatS0 (c := c) hc1 hm hθ0.le hθ1 w :
        UnforcedLeray.B0579.X c m)) =
        xColumnHeatS0Positive hc hm hθ0 hθ1 w.1 :=
      actualWeightedHeatS0_apply_of_pos hc1 hm hθ0 hθ1 w
    have hS : (actualPhysicalWeightedHeatStripSupplier (c := c) (m := m) hc1 hm).S₀ θ w =
        actualWeightedHeatS0 (c := c) hc1 hm hθ0.le hθ1 w := by
      simp only [actualPhysicalWeightedHeatStripSupplier, actualWeightedHeatS0Totalized,
        dif_pos hθ0.le, dif_pos hθ1]
    filter_upwards [h2] with x hx
    rw [hS]
    change ((actualWeightedHeatS0 (c := c) hc1 hm hθ0.le hθ1 w :
      UnforcedLeray.B0579.X c m)) x = _
    rw [hv]
    exact hx
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

end UnforcedLeray.Short.IIIa.Exist
