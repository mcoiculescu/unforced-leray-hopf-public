import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelBoundedCovariance
import UnforcedLeray.Lib.HeatCylinder.H3ActualLimit
import UnforcedLeray.Lib.HeatCylinder.HeatL2Semigroup
import UnforcedLeray.Lib.HeatCylinder.HeatL2Linearity

/-!
# Normalized-cell operator covariance on bounded periodic inputs

The pointwise positive-age covariance descends to the actual normalized-cell L² heat and
heat-divergence operators whenever the periodic input has a bounded continuous representative.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.B0296
open UnforcedLeray.B0289
open UnforcedLeray.HeatCylinder

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The actual normalized-cell heat and heat-divergence CLMs obey the positive-age composition
law on every bounded continuous periodic tensor representative. -/
theorem heatL2CLM_comp_heatDivL2CLM_of_bdd_continuous {c α β : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hβ : 0 < β)
    {T : Plane → Plane × Plane} (hT : Continuous T)
    (hTb : ∃ M : ℝ, ∀ z, ‖T z‖ ≤ M)
    (hper : IsQPeriodic c T) (hmem : MemLp T 2 (cellMeasure c)) :
    heatL2CLM hc α (heatDivL2CLM hc hβ (hmem.toLp T)) =
      heatDivL2CLM hc (add_pos hα hβ) (hmem.toLp T) := by
  rcases hTb with ⟨M, hM⟩
  let outβ : MemLp (heatDiv β T) 2 (cellMeasure c) :=
    periodicHeatDivMemLp hc hβ T hper hT.measurable.aestronglyMeasurable hmem
  have hdivβ := heatDivL2CLM_apply_to_periodic hc hβ hper
    hT.measurable.aestronglyMeasurable hmem
  let g : Plane → Plane := planeRep hc (outβ.toLp (heatDiv β T))
  have hg := planeRep_spec hc (outβ.toLp (heatDiv β T))
  have hgm := memLp_planeRep hc (outβ.toLp (heatDiv β T))
  have hcell : g =ᵐ[cellMeasure c] heatDiv β T := by
    exact hg.2.2.trans outβ.coeFn_toLp
  have hEqPer : IsQPeriodic c (fun z => g z = heatDiv β T z) := by
    intro z
    change (g (z.1 + c, z.2) = heatDiv β T (z.1 + c, z.2)) =
      (g z = heatDiv β T z)
    have hgp : g (z.1 + c, z.2) = g z := by simpa [g] using hg.2.1 z
    have hdp := heatDiv_periodic (θ := β) hper z
    rw [hgp, hdp]
  have hvol := ae_of_ae_cellMeasure hc hEqPer hcell
  have hheatCongr := heat_congr_ae hα hvol
  have hheatMem : MemLp (heat α g) 2 (cellMeasure c) := by
    refine ⟨aestronglyMeasurable_heat c α hg.1.aestronglyMeasurable, ?_⟩
    have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
    have hbound := UnforcedLeray.B0284.eLpNorm_heat_le (θ := α) hc
      hg.2.1 hg.1.aestronglyMeasurable hp ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hbound hgm.eLpNorm_ne_top.lt_top
  let outSum : MemLp (heatDiv (α + β) T) 2 (cellMeasure c) :=
    periodicHeatDivMemLp hc (add_pos hα hβ) T hper
      hT.measurable.aestronglyMeasurable hmem
  have hpoint := heat_heatDiv_of_bdd_continuous hα hβ hT hM
  have hdivSum := heatDivL2CLM_apply_to_periodic hc (add_pos hα hβ) hper
    hT.measurable.aestronglyMeasurable hmem
  have hMid : heatL2 hc α (outβ.toLp (heatDiv β T)) =
      outSum.toLp (heatDiv (α + β) T) := by
    apply Lp.ext
    filter_upwards [hheatMem.coeFn_toLp, outSum.coeFn_toLp] with z hzL hzR
    calc
      (hheatMem.toLp (heat α g) : Plane → Plane) z = heat α g z := hzL
      _ = heat α (heatDiv β T) z := congrFun hheatCongr z
      _ = heatDiv (α + β) T z := by
        rw [heat_apply_of_pos hα]
        exact hpoint z
      _ = (outSum.toLp (heatDiv (α + β) T) : Plane → Plane) z := hzR.symm
  have hleft0 := congrArg (heatL2CLM hc α) hdivβ
  have hleft1 : heatL2CLM hc α (outβ.toLp (heatDiv β T)) =
      heatL2 hc α (outβ.toLp (heatDiv β T)) := by
    rw [heatL2CLM_apply]
  calc
    heatL2CLM hc α (heatDivL2CLM hc hβ (hmem.toLp T)) =
        heatL2CLM hc α (outβ.toLp (heatDiv β T)) := hleft0
    _ = heatL2 hc α (outβ.toLp (heatDiv β T)) := hleft1
    _ = outSum.toLp (heatDiv (α + β) T) := hMid
    _ = heatDivL2CLM hc (add_pos hα hβ) (hmem.toLp T) := hdivSum.symm

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.heatL2CLM_comp_heatDivL2CLM_of_bdd_continuous
