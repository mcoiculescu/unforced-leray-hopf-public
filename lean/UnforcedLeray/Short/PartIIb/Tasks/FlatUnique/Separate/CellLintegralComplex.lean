import UnforcedLeray.Short.PartIIb.Sub.T11_6

/-!
# Part II-b, `PartII-b:T11/6/4` (strip of the plane as a cell of `ℝ × ℝ`)

Target: `UnforcedLeray.Short.IIb.CellLintegralComplex` (defined in `Sub/T11_6.lean`).
Source: classical identification `ℂ ≃ ℝ × ℝ`, used in the 2D Liouville step
(`the November 2 reference manuscript`, SP 2618).

Proof: `Complex.measurableEquivRealProd` is measure preserving (`volume` to `volume`), its
preimage of `Cyl.cell c = Ico (-c/2) (c/2) ×ˢ univ` is the strip `{z | z.re ∈ Ico (-(c/2)) (c/2)}`
(`neg_div`), and `MeasurePreserving.setLIntegral_comp_preimage` transports the set integral.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem cellLintegralComplex : UnforcedLeray.Short.IIb.CellLintegralComplex := by
  intro c G hG
  have hmp : MeasurePreserving Complex.measurableEquivRealProd volume volume :=
    Complex.volume_preserving_equiv_real_prod
  have hs : MeasurableSet (UnforcedLeray.Cyl.cell c) := by
    unfold UnforcedLeray.Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hset : Complex.measurableEquivRealProd ⁻¹' UnforcedLeray.Cyl.cell c
      = {z : ℂ | z.re ∈ Ico (-(c / 2)) (c / 2)} := by
    ext z
    simp [UnforcedLeray.Cyl.cell, neg_div]
  have key := hmp.setLIntegral_comp_preimage (f := G) hs hG
  rw [hset] at key
  exact key

end UnforcedLeray.Short.IIb

end
