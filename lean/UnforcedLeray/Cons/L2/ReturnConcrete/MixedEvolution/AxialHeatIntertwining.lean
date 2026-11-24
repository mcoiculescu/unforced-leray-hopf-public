import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialWeightedInput
import UnforcedLeray.Lib.HeatCylinder.HeatL2Linearity

/-!
# Actual Gaussian image of the axial weighted input

The normalized-cell heat operator applied to the constructed axial weighted input is represented
by literal B0284 heat of the same periodic lift. This pins the unweighted heat term in the axial
conjugation argument to the actual cylinder field.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

private theorem heatL2CLM_value_ae {c θ : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (B0284.cellMeasure c)) :
    (HeatCylinder.heatL2CLM hc θ x : Plane → Plane) =ᵐ[B0284.cellMeasure c]
      B0284.heat θ (HeatCylinder.planeRep hc x) := by
  have hmem := HeatCylinder.memLp_planeRep hc x
  have hheat : MemLp (B0284.heat θ (HeatCylinder.planeRep hc x)) 2
      (B0284.cellMeasure c) := by
    refine ⟨B0296.aestronglyMeasurable_heat c θ
      (HeatCylinder.planeRep_spec hc x).1.aestronglyMeasurable, ?_⟩
    have hcontract := B0284.eLpNorm_heat_le (θ := θ) hc
      (HeatCylinder.planeRep_spec hc x).2.1
      (HeatCylinder.planeRep_spec hc x).1.aestronglyMeasurable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top
  change (hheat.toLp (B0284.heat θ (HeatCylinder.planeRep hc x)) : Plane → Plane) =ᵐ[
    B0284.cellMeasure c] B0284.heat θ (HeatCylinder.planeRep hc x)
  exact hheat.coeFn_toLp

/-- On the actual normalized-cell carrier, the heat of the axial weighted input is the literal
B0284 Gaussian convolution of its selected physical lift. -/
theorem axialWeightedHeatInput_heat_value_ae {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (f : X c m) :
    (HeatCylinder.heatL2CLM hc θ (axialWeightedHeatInput hc hm f) : Plane → Plane) =ᵐ[
      B0284.cellMeasure c]
      B0284.heat θ (fun z => axialWeight m z • xColumnHeatLift hc f z) := by
  have hsel := HeatCylinder.planeRep_spec hc (axialWeightedHeatInput hc hm f)
  have hinput := coeFn_axialWeightedHeatInput hc hm f
  have hperInput : B0284.IsQPeriodic c
      (fun z => axialWeight m z • xColumnHeatLift hc f z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) =
      axialWeight m z • xColumnHeatLift hc f z
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z]
  have hglobal : HeatCylinder.planeRep hc (axialWeightedHeatInput hc hm f) =ᵐ[volume]
      fun z => axialWeight m z • xColumnHeatLift hc f z := by
    apply B0289.ae_of_ae_cellMeasure hc
    · intro z
      change (HeatCylinder.planeRep hc (axialWeightedHeatInput hc hm f) (z.1 + c, z.2) =
        axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2)) =
        (HeatCylinder.planeRep hc (axialWeightedHeatInput hc hm f) z =
        axialWeight m z • xColumnHeatLift hc f z)
      have hrepPer := hsel.2.1 z
      have hfieldPer := hperInput z
      change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) =
        axialWeight m z • xColumnHeatLift hc f z at hfieldPer
      rw [hrepPer, hfieldPer]
    · exact hsel.2.2.trans hinput
  have hheat : B0284.heat θ (HeatCylinder.planeRep hc
      (axialWeightedHeatInput hc hm f)) =ᵐ[volume]
      B0284.heat θ (fun z => axialWeight m z • xColumnHeatLift hc f z) := by
    by_cases hθ : 0 < θ
    · exact Filter.Eventually.of_forall fun z =>
        congrFun (B0289.heat_congr_ae hθ hglobal) z
    · have h0 : θ ≤ 0 := le_of_not_gt hθ
      filter_upwards [hglobal] with z hz
      rw [B0284.heat_of_nonpos h0, B0284.heat_of_nonpos h0]
      exact hz
  have hvalue := heatL2CLM_value_ae (c := c) (θ := θ) hc
    (axialWeightedHeatInput hc hm f)
  have hheatCell := (B0284.cellMeasure_ac c).ae_le hheat
  exact hvalue.trans hheatCell

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialWeightedHeatInput_heat_value_ae

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
