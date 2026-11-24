import UnforcedLeray.Lib.HeatCylinder.H3Operator

/-!
# Measurability of actual positive heat-age cylinder orbits

The orbit below is the actual Gaussian divergence kernel on the normalized cylinder `L²`
quotient. Its measurability follows from the already-proved jointly measurable kernel and slice
theorem, with the heat age represented as `(-1) * (0 - θ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- Actual `B0296.heatDiv` output class along a fixed periodic tensor, extended by zero for
nonpositive ages as in the concrete heat kernel definition. -/
noncomputable def heatDivL2Orbit {c : ℝ} (hc : 0 < c)
    {T : Plane → Plane × Plane} (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : Measurable T) (hmem : MemLp T 2
      (UnforcedLeray.B0284.cellMeasure c)) (θ : ℝ) :
    Lp (Plane) 2 (UnforcedLeray.B0284.cellMeasure c) :=
  let Tpath : ℝ × Plane → Plane × Plane := fun p => T p.2
  let hTpathMeas : Measurable Tpath := hmeas.comp measurable_snd
  let hTpathPer : ∀ t : ℝ, UnforcedLeray.B0284.IsQPeriodic c (fun z => Tpath (t, z)) :=
    fun _ => hper
  let hTpathMem : ∀ t : ℝ, MemLp (fun z => Tpath (t, z)) 2
      (UnforcedLeray.B0284.cellMeasure c) := fun _ => hmem
  (memLp_heatDiv_timePath hc hTpathMeas hTpathPer hTpathMem θ).toLp
    (fun z => UnforcedLeray.B0296.heatDiv ((-1 : ℝ) * (0 - θ)) T z)

/-- For every fixed measurable periodic tensor with finite normalized-cell `L²` norm, its actual
Gaussian `heatDiv` orbit is strongly measurable in heat age. Restricting to positive ages gives
the interface used by the train Duhamel integrand. -/
theorem aestronglyMeasurable_heatDivL2Orbit {c : ℝ} (hc : 0 < c)
    {T : Plane → Plane × Plane} (hper : UnforcedLeray.B0284.IsQPeriodic c T)
    (hmeas : Measurable T) (hmem : MemLp T 2
      (UnforcedLeray.B0284.cellMeasure c)) :
    AEStronglyMeasurable (heatDivL2Orbit hc hper hmeas hmem)
      (volume.restrict (Ioi 0)) := by
  let Tpath : ℝ × Plane → Plane × Plane := fun p => T p.2
  have hTpathMeas : Measurable Tpath := hmeas.comp measurable_snd
  have hTpathPer : ∀ t : ℝ, UnforcedLeray.B0284.IsQPeriodic c (fun z => Tpath (t, z)) :=
    fun _ => hper
  have hTpathMem : ∀ t : ℝ, MemLp (fun z => Tpath (t, z)) 2
      (UnforcedLeray.B0284.cellMeasure c) := fun _ => hmem
  have horbit := aestronglyMeasurable_heatDivL2_path hc hTpathMeas hTpathPer hTpathMem
    (ν := -1) (s := 0)
  have hrestrict : AEStronglyMeasurable
      (fun θ : ℝ => (memLp_heatDiv_timePath hc hTpathMeas hTpathPer hTpathMem θ).toLp
        (fun z => UnforcedLeray.B0296.heatDiv ((-1 : ℝ) * (0 - θ))
          (fun y => Tpath (θ, y)) z)) (volume.restrict (Ioi 0)) :=
    horbit.mono_ac (show (volume.restrict (Ioi 0)) ≪ volume from
      Measure.absolutelyContinuous_restrict)
  exact hrestrict.congr (Filter.Eventually.of_forall fun θ => by
    simp only [heatDivL2Orbit]
    rfl)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.aestronglyMeasurable_heatDivL2Orbit
