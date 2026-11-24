import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Needed

/-!
# N4: periodic heat on the normalized cell, scalar Plane carrier

Proof of `NeedHeatPeriodicL2` from `Needed.lean`, mirroring
`heatDivL2CLM_apply_to_periodic` (`Lib/HeatCylinder/H3ActualLimit.lean`) with `heat` in place of
`heatDiv`. The L² operator `heatL2CLM` is computed on a measurable periodic representative
`R = planeRep hc (hmem.toLp T)`; `R` agrees with `T` a.e. on the cell, hence a.e. on `volume` by
periodicity, and `heat` respects a.e. equality (for `θ > 0`; for `θ ≤ 0` it is the identity).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.HeatCylinder

theorem needHeatPeriodicL2 : NeedHeatPeriodicL2 := by
  intro c hc θ T hper hmeas hmem
  set x : Lp Plane 2 (UnforcedLeray.B0284.cellMeasure c) := hmem.toLp T with hx
  set R := planeRep hc x with hRdef
  have hR := planeRep_spec hc x
  have hRmem := memLp_planeRep hc x
  have hRae : R =ᵐ[UnforcedLeray.B0284.cellMeasure c] T := by
    filter_upwards [hR.2.2, hmem.coeFn_toLp] with z hRx hTx
    exact hRx.trans hTx
  have hperEq : UnforcedLeray.B0284.IsQPeriodic c (fun z => R z = T z) := by
    intro z
    have hRper : R (z.1 + c, z.2) = R z := hR.2.1 z
    have hTper : T (z.1 + c, z.2) = T z := hper z
    simp [hRper, hTper]
  have hRvol := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperEq hRae
  -- the heat output of the periodic representative is in normalized-cell L²
  have hheatR : MemLp (UnforcedLeray.B0284.heat θ R) 2 (UnforcedLeray.B0284.cellMeasure c) := by
    refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ hR.1.aestronglyMeasurable, ?_⟩
    have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hR.2.1
      hR.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hRmem.eLpNorm_ne_top.lt_top
  -- heat of the representative and heat of `T` agree a.e. on the cell
  have hae : UnforcedLeray.B0284.heat θ R =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      UnforcedLeray.B0284.heat θ T := by
    by_cases hθ : 0 < θ
    · have hfun : UnforcedLeray.B0284.heat θ R = UnforcedLeray.B0284.heat θ T :=
        UnforcedLeray.B0289.heat_congr_ae hθ hRvol
      exact Filter.Eventually.of_forall fun z => congrFun hfun z
    · filter_upwards [hRae] with z hz
      simp [UnforcedLeray.B0284.heat, hθ, hz]
  have hh : MemLp (UnforcedLeray.B0284.heat θ T) 2 (UnforcedLeray.B0284.cellMeasure c) :=
    hheatR.ae_eq hae
  refine ⟨hh, ?_⟩
  rw [UnforcedLeray.HeatCylinder.heatL2CLM_apply]
  apply Lp.ext
  have h1 : (heatL2 hc θ x : Plane → Plane) =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      UnforcedLeray.B0284.heat θ R :=
    hheatR.coeFn_toLp
  have h2 : (hh.toLp (UnforcedLeray.B0284.heat θ T) : Plane → Plane) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] UnforcedLeray.B0284.heat θ T :=
    hh.coeFn_toLp
  filter_upwards [h1, h2, hae] with z e1 e2 e3
  exact e1.trans (e3.trans e2.symm)

end UnforcedLeray.Short.PartI
