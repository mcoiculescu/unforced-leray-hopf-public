import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.Props

/-!
# `AgeMeasureAC` (item `PartIII-b:C/near/delta/7/4`)

Source `the November 2 reference manuscript` 3426-3440: the age measure
`ageμ c a = s^a ds ⊗ c⁻¹ dq dη` is absolutely continuous w.r.t. Lebesgue measure on
`(0,∞) × cell c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem ageMeasureAC : AgeMeasureAC := by
  intro c a hc
  have hset : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  have hcell : UnforcedLeray.Cyl.avgμ c ≪ volume.restrict (UnforcedLeray.B0579.cell c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [← hset]
    exact Measure.smul_absolutelyContinuous
  have hdens : ((volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ a)) ≪
      volume.restrict (Ioi (0 : ℝ)) :=
    withDensity_absolutelyContinuous _ _
  have hprod := Measure.AbsolutelyContinuous.prod hdens hcell
  unfold ageμ
  rw [Measure.prod_restrict] at hprod
  exact hprod

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
