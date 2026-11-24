import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatCirculation
import UnforcedLeray.Lib.HeatCylinder.HeatL2SemigroupClosed

/-!
# Semigroup compatibility of the actual weighted heat family

This leaf connects positive weighted heat outputs to the normalized-cell Gaussian heat semigroup.
Weighted strong continuity at age zero remains a separate theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.GaussianVortex (Plane)

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

private theorem heatL2_value_ae {c θ : ℝ} (hc : 0 < c)
    (x : Lp Plane 2 (UnforcedLeray.B0284.cellMeasure c)) :
    (HeatCylinder.heatL2 hc θ x : Plane → Plane) =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      UnforcedLeray.B0284.heat θ (HeatCylinder.planeRep hc x) := by
  let f := HeatCylinder.planeRep hc x
  have hf := HeatCylinder.planeRep_spec hc x
  have hm := HeatCylinder.memLp_planeRep hc x
  have hh : MemLp (UnforcedLeray.B0284.heat θ f) 2
      (UnforcedLeray.B0284.cellMeasure c) := by
    refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ
      hf.1.aestronglyMeasurable, ?_⟩
    have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hf.2.1
      hf.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hm.eLpNorm_ne_top.lt_top
  change hh.toLp (UnforcedLeray.B0284.heat θ f) =ᵐ[
    UnforcedLeray.B0284.cellMeasure c] UnforcedLeray.B0284.heat θ f
  exact hh.coeFn_toLp

/-- The concrete normalized-cell embedding remembers the entire weighted vorticity column. -/
theorem xColumnHeatInput_injective {c m : ℝ} (hc : 0 < c) (hm : 1 ≤ m) :
    Function.Injective (xColumnHeatInput hc hm) := by
  intro f g h
  apply Lp.ext
  have hfun : xColumnHeatInput hc hm f =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      xColumnHeatInput hc hm g := by
    simpa [h]
  have hrep : xColumnPeriodicRep hc f =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      xColumnPeriodicRep hc g := by
    filter_upwards [coeFn_xColumnHeatInput hc hm f, hfun,
      coeFn_xColumnHeatInput hc hm g] with z hf hfg hg
    exact congrArg Prod.fst (hf.symm.trans (hfg.trans hg))
  have hper : UnforcedLeray.B0284.IsQPeriodic c (fun z =>
      xColumnPeriodicRep hc f z = xColumnPeriodicRep hc g z) := by
    intro z
    change (xColumnPeriodicRep hc f (z.1 + c, z.2) =
      xColumnPeriodicRep hc g (z.1 + c, z.2)) =
        (xColumnPeriodicRep hc f z = xColumnPeriodicRep hc g z)
    rw [periodic_xColumnPeriodicRep hc f z, periodic_xColumnPeriodicRep hc g z]
  have hglobal := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hper hrep
  have hglobalCenter : xColumnPeriodicRep hc f =ᵐ[Cyl.cellμ c]
      xColumnPeriodicRep hc g :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le hglobal
  have hfg : (f : Plane → ℝ) =ᵐ[Cyl.cellμ c] (g : Plane → ℝ) :=
    (xColumnPeriodicRep_ae_eq hc f).symm.trans
      (hglobalCenter.trans (xColumnPeriodicRep_ae_eq hc g))
  have hfgWeighted : (f : Plane → ℝ) =ᵐ[UnforcedLeray.B0579.cellMeasure c m]
      (g : Plane → ℝ) := by
    have hfg' : (f : Plane → ℝ) =ᵐ[volume.restrict (UnforcedLeray.B0579.cell c)]
        (g : Plane → ℝ) := by
      simpa [Cyl.cellμ, Cyl.cell, UnforcedLeray.B0579.cell,
        show -(c / 2) = -c / 2 by ring] using hfg
    exact (UnforcedLeray.B0579.cellMeasure_ac c m).ae_le hfg'
  exact hfgWeighted

/-- The weighted positive-age heat output, embedded into normalized-cell `L²`, is exactly the
actual normalized-cell Gaussian heat applied to the embedded input. -/
theorem xColumnHeatInput_positive_eq_heatL2 {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (f : UnforcedLeray.B0579.X c m) :
    xColumnHeatInput hc hm (xColumnHeatS0Positive hc hm hθ hθ1 f) =
      HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f) := by
  apply Lp.ext
  have hleft := coeFn_xColumnHeatInput hc hm
    (xColumnHeatS0Positive hc hm hθ hθ1 f)
  have hinput := (HeatCylinder.planeRep_spec hc (xColumnHeatInput hc hm f)).2.2.trans
    (coeFn_xColumnHeatInput hc hm f)
  have hinputGlobal : HeatCylinder.planeRep hc (xColumnHeatInput hc hm f) =ᵐ[volume]
      xColumnHeatLift hc f := by
    apply UnforcedLeray.B0289.ae_of_ae_cellMeasure hc
    · intro z
      apply propext
      constructor
      · intro hz
        calc
          HeatCylinder.planeRep hc (xColumnHeatInput hc hm f) z =
              HeatCylinder.planeRep hc (xColumnHeatInput hc hm f) (z.1 + c, z.2) :=
                (HeatCylinder.planeRep_spec hc (xColumnHeatInput hc hm f)).2.1 z |>.symm
          _ = xColumnHeatLift hc f (z.1 + c, z.2) := hz
          _ = xColumnHeatLift hc f z := periodic_xColumnHeatLift hc f z
      · intro hz
        calc
          HeatCylinder.planeRep hc (xColumnHeatInput hc hm f) (z.1 + c, z.2) =
              HeatCylinder.planeRep hc (xColumnHeatInput hc hm f) z :=
                (HeatCylinder.planeRep_spec hc (xColumnHeatInput hc hm f)).2.1 z
          _ = xColumnHeatLift hc f z := hz
          _ = xColumnHeatLift hc f (z.1 + c, z.2) :=
                (periodic_xColumnHeatLift hc f z).symm
    · exact hinput
  have hheatCong := UnforcedLeray.B0289.heat_congr_ae hθ hinputGlobal
  have hheatCongAE : UnforcedLeray.B0284.heat θ
      (HeatCylinder.planeRep hc (xColumnHeatInput hc hm f)) =ᵐ[volume]
      UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) :=
    Filter.Eventually.of_forall fun z => congrFun hheatCong z
  have hright := heatL2_value_ae (θ := θ) hc (xColumnHeatInput hc hm f)
  have hplaneOutput : HeatCylinder.planeRep hc
      (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c]
      (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f) : Plane → Plane) :=
    (HeatCylinder.planeRep_spec hc _).2.2
  have hplaneHeat : HeatCylinder.planeRep hc
      (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c]
      UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) := by
    exact hplaneOutput.trans (hright.trans
      ((UnforcedLeray.B0284.cellMeasure_ac c).ae_le hheatCongAE))
  have hplaneHeatGlobal : HeatCylinder.planeRep hc
      (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) =ᵐ[volume]
      UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) := by
    apply UnforcedLeray.B0289.ae_of_ae_cellMeasure hc
    · intro z
      apply propext
      constructor
      · intro hz
        calc
          HeatCylinder.planeRep hc
              (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) z =
              HeatCylinder.planeRep hc
                (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) (z.1 + c, z.2) :=
                  (HeatCylinder.planeRep_spec hc _).2.1 z |>.symm
          _ = UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) (z.1 + c, z.2) := hz
          _ = UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z :=
                UnforcedLeray.B0284.heat_periodic (periodic_xColumnHeatLift hc f) z
      · intro hz
        calc
          HeatCylinder.planeRep hc
              (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) (z.1 + c, z.2) =
              HeatCylinder.planeRep hc
                (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) z :=
                  (HeatCylinder.planeRep_spec hc _).2.1 z
          _ = UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) z := hz
          _ = UnforcedLeray.B0284.heat θ (xColumnHeatLift hc f) (z.1 + c, z.2) :=
                (UnforcedLeray.B0284.heat_periodic (periodic_xColumnHeatLift hc f) z).symm
    · exact hplaneHeat
  have hsecond := heat_xColumnHeatLift_snd_ae_zero hc hm hθ f
  have hscalar := xColumnHeatS0Positive_periodicRep_eq_heatL2CLMRep
    hc hm hθ hθ1 f
  have hvec : xColumnHeatLift hc
      (xColumnHeatS0Positive hc hm hθ hθ1 f) =ᵐ[volume]
      HeatCylinder.planeRep hc
        (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) := by
    filter_upwards [hscalar, hplaneHeatGlobal, hsecond] with z hfst hpair hsnd0
    have hsnd : (HeatCylinder.planeRep hc
        (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) z).2 = 0 := by
      rw [hpair]
      exact hsnd0
    change (xColumnPeriodicRep hc
        (xColumnHeatS0Positive hc hm hθ hθ1 f) z, (0 : ℝ)) =
      HeatCylinder.planeRep hc
        (HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f)) z
    exact Prod.ext hfst hsnd.symm
  have hvecCell := (UnforcedLeray.B0284.cellMeasure_ac c).ae_le hvec
  filter_upwards [hleft, hvecCell, hplaneOutput] with z hl hv hp
  exact hl.trans (hv.trans hp)

/-- The actual weighted Gaussian outputs obey the positive-age semigroup law whenever all ages
remain in the short-strip range where the concrete weighted operator is defined. -/
theorem xColumnHeatS0Positive_comp_of_pos {c m α β : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hα : 0 < α) (hβ : 0 < β)
    (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hsum1 : α + β ≤ 1)
    (f : UnforcedLeray.B0579.X c m) :
    xColumnHeatS0Positive hc hm (add_pos hα hβ) hsum1 f =
      xColumnHeatS0Positive hc hm hα hα1
        (xColumnHeatS0Positive hc hm hβ hβ1 f) := by
  apply xColumnHeatInput_injective hc hm
  rw [xColumnHeatInput_positive_eq_heatL2 hc hm (add_pos hα hβ) hsum1 f]
  rw [xColumnHeatInput_positive_eq_heatL2 hc hm hα hα1
    (xColumnHeatS0Positive hc hm hβ hβ1 f)]
  rw [xColumnHeatInput_positive_eq_heatL2 hc hm hβ hβ1 f]
  exact (HeatCylinder.heatL2_comp_of_pos hc hα hβ
    (xColumnHeatInput hc hm f)).symm

/-- The same short-age heat semigroup law on the actual zero-circulation state space. -/
theorem actualWeightedHeatS0_comp_of_pos {c m α β : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hα : 0 < α) (hβ : 0 < β)
    (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hsum1 : α + β ≤ 1)
    (w : ActualVorticity (c := c) (m := m) hm) :
    actualWeightedHeatS0 (c := c) hc1 hm (le_of_lt hα) hα1
      (actualWeightedHeatS0 (c := c) hc1 hm (le_of_lt hβ) hβ1 w) =
    actualWeightedHeatS0 (c := c) hc1 hm (le_of_lt (add_pos hα hβ)) hsum1 w := by
  apply Subtype.ext
  rw [actualWeightedHeatS0_apply_of_pos (c := c) (m := m) hc1 hm hα hα1
    (actualWeightedHeatS0 (c := c) hc1 hm (le_of_lt hβ) hβ1 w)]
  rw [actualWeightedHeatS0_apply_of_pos (c := c) (m := m) hc1 hm hβ hβ1 w]
  rw [actualWeightedHeatS0_apply_of_pos (c := c) (m := m) hc1 hm
    (add_pos hα hβ) hsum1 w]
  exact (xColumnHeatS0Positive_comp_of_pos (Fact.out : 0 < c) hm hα hβ
    hα1 hβ1 hsum1 w.1).symm

/-- The actual physical `S₀` CLMs satisfy the full nonnegative short-strip semigroup law,
including either zero-age endpoint. -/
theorem actualWeightedHeatS0_comp_of_nonneg {c m α β : ℝ} [Fact (0 < c)]
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hsum1 : α + β ≤ 1) :
    (actualWeightedHeatS0 (c := c) hc1 hm hα0 hα1).comp
      (actualWeightedHeatS0 (c := c) hc1 hm hβ0 hβ1) =
    actualWeightedHeatS0 (c := c) hc1 hm (add_nonneg hα0 hβ0) hsum1 := by
  apply ContinuousLinearMap.ext
  intro w
  by_cases hα : α = 0
  · subst α
    simp [actualWeightedHeatS0_zero]
  · by_cases hβ : β = 0
    · subst β
      simp [actualWeightedHeatS0_zero]
    · have hαpos : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hα)
      have hβpos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ)
      exact actualWeightedHeatS0_comp_of_pos (c := c) (m := m) hc1 hm
        hαpos hβpos hα1 hβ1 hsum1 w

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatInput_positive_eq_heatL2
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatInput_injective
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatS0Positive_comp_of_pos
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0_comp_of_pos
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.actualWeightedHeatS0_comp_of_nonneg
