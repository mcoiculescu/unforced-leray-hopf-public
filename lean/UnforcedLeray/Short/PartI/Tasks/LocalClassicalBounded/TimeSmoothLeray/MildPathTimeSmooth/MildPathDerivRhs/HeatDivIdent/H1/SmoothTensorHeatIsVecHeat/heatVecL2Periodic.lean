import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1_2
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2
import UnforcedLeray.Lib.HeatCylinder.HeatL2Linearity
import UnforcedLeray.Lib.HeatCylinder.HeatL2Operator
import UnforcedLeray.Units.B0289.Semigroup
import UnforcedLeray.Units.B0289.Periodize
import UnforcedLeray.Units.B0284.Contraction
import UnforcedLeray.Units.B0296.Conv

/-!
# `heatVecL2Periodic`: vector heat on a periodic `L²` field

Source of record: `the November 2 reference manuscript`, lines 3594-3625.
Vector version of the periodic action of `heatL2CLM` (cf. `heatDivVecL2CLM_apply_to_periodic`,
`H3ActualLimit.lean`, and `needHeatPeriodicL2`, `N4.lean`), proved self-contained.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.HeatCylinder

theorem heatVecL2Periodic : HeatVecL2Periodic := by
  intro c θ hc hθ R hper _hcont hmem
  -- the plane class of `R`
  have hRL : MemLp R 2 (UnforcedLeray.B0284.cellMeasure c) := by
    have h1 : MemLp (fun z => (Train.toVecL.symm : Vec →L[ℝ] Plane) (toVec (R z))) 2
        (UnforcedLeray.B0284.cellMeasure c) :=
      (Train.toVecL.symm : Vec →L[ℝ] Plane).comp_memLp' hmem
    refine (memLp_congr_ae ?_).mp h1
    exact Filter.Eventually.of_forall fun z => (Train.toVecL.symm_apply_apply (R z)).symm
  have hX : (Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2
      (UnforcedLeray.B0284.cellMeasure c) (hmem.toLp (fun z => toVec (R z))) = hRL.toLp R := by
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (Train.toVecL.symm : Vec →L[ℝ] Plane) (hmem.toLp (fun z => toVec (R z))),
      hRL.coeFn_toLp, hmem.coeFn_toLp] with z e1 e2 e3
    rw [e1, e2, e3]
    exact Train.toVecL.symm_apply_apply (R z)
  -- the periodic measurable representative of the plane class
  set x : Lp Plane 2 (UnforcedLeray.B0284.cellMeasure c) := hRL.toLp R with hx
  set P := planeRep hc x with hPdef
  have hP := planeRep_spec hc x
  have hPmem := memLp_planeRep hc x
  have hPae : P =ᵐ[UnforcedLeray.B0284.cellMeasure c] R := by
    filter_upwards [hP.2.2, hRL.coeFn_toLp] with z hPx hRx
    exact hPx.trans hRx
  have hperEq : UnforcedLeray.B0284.IsQPeriodic c (fun z => P z = R z) := by
    intro z
    have hPper : P (z.1 + c, z.2) = P z := hP.2.1 z
    have hRper : R (z.1 + c, z.2) = R z := hper z
    simp [hPper, hRper]
  have hPvol := UnforcedLeray.B0289.ae_of_ae_cellMeasure hc hperEq hPae
  -- heat of the periodic representative
  have hheatP : MemLp (UnforcedLeray.B0284.heat θ P) 2 (UnforcedLeray.B0284.cellMeasure c) := by
    refine ⟨UnforcedLeray.B0296.aestronglyMeasurable_heat c θ hP.1.aestronglyMeasurable, ?_⟩
    have hcontract := UnforcedLeray.B0284.eLpNorm_heat_le (θ := θ) hc hP.2.1
      hP.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top
    exact lt_of_le_of_lt hcontract hPmem.eLpNorm_ne_top.lt_top
  have hfun : UnforcedLeray.B0284.heat θ P = UnforcedLeray.B0284.heat θ R :=
    UnforcedLeray.B0289.heat_congr_ae hθ hPvol
  have hae : UnforcedLeray.B0284.heat θ P =ᵐ[UnforcedLeray.B0284.cellMeasure c]
      UnforcedLeray.B0284.heat θ R :=
    Filter.Eventually.of_forall fun z => congrFun hfun z
  have hhP : MemLp (UnforcedLeray.B0284.heat θ R) 2 (UnforcedLeray.B0284.cellMeasure c) :=
    hheatP.ae_eq hae
  -- the plane operator on `R`
  have hEq : heatL2CLM hc θ (hRL.toLp R) = hhP.toLp (UnforcedLeray.B0284.heat θ R) := by
    rw [heatL2CLM_apply]
    apply Lp.ext
    filter_upwards [hheatP.coeFn_toLp, hhP.coeFn_toLp, hae] with z e1 e2 e3
    exact e1.trans (e3.trans e2.symm)
  -- the vector witness
  have hh : MemLp (fun z => toVec (UnforcedLeray.B0284.heat θ R z)) 2
      (UnforcedLeray.B0284.cellMeasure c) :=
    (Train.toVecL : Plane →L[ℝ] Vec).comp_memLp' hhP
  refine ⟨hh, ?_⟩
  rw [heatVecL2CLM_apply, hX, hEq]
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (Train.toVecL : Plane →L[ℝ] Vec)
    (hhP.toLp (UnforcedLeray.B0284.heat θ R)), hhP.coeFn_toLp, hh.coeFn_toLp] with z e1 e2 e3
  rw [e1, e2, e3] <;> rfl

end UnforcedLeray.Short.PartI
