import UnforcedLeray.Short.PartIIb.Sub.T11_6

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- Leaf `PartII-b:T11/6/18`: `hMeas c r` is carried by `{x.1 > 0}` and is absolutely continuous
with respect to Lebesgue measure there. Proof: `hMeas c r` is a product of the weighted measure
`(volume.restrict (Ioi 0)).withDensity w` with `Cyl.avgμ c`, which is absolutely continuous with
respect to `volume.restrict (Ioi 0 ×ˢ univ)`. -/
theorem hMeasAe : UnforcedLeray.Short.IIb.HMeasAe := by
  intro c r P hc hP
  have hA : ((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ (r / 2 - 5 / 2))) ≪ (volume.restrict (Ioi (0 : ℝ))) :=
    withDensity_absolutelyContinuous _ _
  have hB : Cyl.avgμ c ≪ (volume : Measure (ℝ × ℝ)) := by
    refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
    simp [Cyl.avgμ, Cyl.cellμ, Measure.smul_apply, Measure.restrict_apply hs,
      measure_inter_null_of_null_left _ hs0]
  have hac : hMeas c r ≪ (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ)) :=
    Measure.AbsolutelyContinuous.prod hA hB
  have hvol : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ)) =
      (volume : Measure Coord).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
    calc (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (ℝ × ℝ))
        = (volume.restrict (Ioi (0 : ℝ))).prod ((volume : Measure (ℝ × ℝ)).restrict univ) := by
          rw [Measure.restrict_univ]
      _ = ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))).restrict
            (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := Measure.prod_restrict _ _
      _ = (volume : Measure Coord).restrict (Ioi (0 : ℝ) ×ˢ univ) := rfl
  rw [hvol] at hac
  have h1 : ∀ᵐ x ∂((volume : Measure Coord).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))), P x := by
    rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)]
    filter_upwards [hP] with x hx hxm
    exact hx hxm.1
  exact hac.ae_le h1

end UnforcedLeray.Short.IIb
