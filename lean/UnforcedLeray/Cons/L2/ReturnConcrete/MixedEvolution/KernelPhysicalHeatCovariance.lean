import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelFluxL2Covariance
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatResponse
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedHeatOperator

/-!
# Weighted physical S₀/response covariance bridge

This leaf connects the already proved normalized-cell identity back to the literal weighted
zero-circulation state and signed response maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.B0296
open UnforcedLeray.B0579 hiding Plane

/-- The second coordinate of the actual signed heat-divergence vanishes on the concrete scalar
flux tensor embedding. -/
theorem negativeHeatDiv_scalarFluxTensor_snd {θ : ℝ} (hθ : 0 < θ)
    (Fq Fη : Plane → ℝ) (z : Plane) :
    (negativeHeatDiv θ (scalarFluxTensor Fq Fη) z).2 = 0 := by
  rw [negativeHeatDiv, heatDiv_apply_of_pos hθ]
  let π₂ : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let g : Plane → Plane := fun w =>
    divKernel θ w (scalarFluxTensor Fq Fη (z - w))
  change π₂ (-(∫ w : Plane, g w)) = 0
  by_cases hi : Integrable g volume
  · rw [map_neg, ← π₂.integral_comp_comm hi]
    have hzero : (fun w : Plane => π₂ (g w)) = 0 := by
      funext w
      rw [show g w = divKernel θ w (scalarFluxTensor Fq Fη (z - w)) by rfl,
        divKernel_scalarFluxTensor]
      rfl
    simp [hzero]
  · rw [integral_undef hi]
    simp

/-- The actual B0284 Gaussian heat preserves a zero second coordinate, including when the
pointwise Bochner integral is undefined (in which case it is zero by definition). -/
theorem heat_snd_eq_zero_of_snd_eq_zero {θ : ℝ} (hθ : 0 < θ)
    (f : Plane → Plane) (hf : ∀ z, (f z).2 = 0) (z : Plane) :
    (B0284.heat θ f z).2 = 0 := by
  rw [B0284.heat_apply_of_pos hθ]
  let π₂ : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let g : Plane → Plane := fun w => B0284.heatKernel2 θ w • f (z - w)
  change π₂ (∫ w : Plane, g w) = 0
  by_cases hi : Integrable g volume
  · rw [← π₂.integral_comp_comm hi]
    have hzero : (fun w : Plane => π₂ (g w)) = 0 := by
      funext w
      simp [g, π₂, hf]
    simp [hzero]
  · rw [integral_undef hi]
    simp

/-- The normalized-cell realization of the actual weighted scalar response equals the full
signed B0296 response, after identifying the scalar output with the first component and using
the exact zero second-coordinate identity. -/
theorem xColumnHeatInput_xFluxNegativeHeatDivXCLM_eq {c m θ : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (F : Fin 2 → X c m) :
    xColumnHeatInput hc hm (xFluxNegativeHeatDivXCLM hc hm hθ hθ1 F) =
      xFluxNegativeHeatDivL2CLM hc hm hθ F := by
  let T := xFluxPeriodicTensor hc F
  let out := xFluxNegativeHeatDivXCLM hc hm hθ hθ1 F
  have hXeq := xFluxNegativeHeatDivXCLM_apply_eq_actual hc hm hθ hθ1 F
  have hXae := Lp.ext_iff.mp hXeq
  let houtMem := memLp_xFlux_negativeHeatDiv_fst_X hc hm hθ hθ1 F
  let f : Plane → ℝ := fun z => (negativeHeatDiv θ T z).1
  have hXc : (out : Plane → ℝ) =ᵐ[Cyl.cellμ c]
      f := by
    have h0 := (cellMeasure_ac_cellMeasure c 0 m).ae_le hXae
    have hμ : cellMeasure c 0 = Cyl.cellμ c := by
      rw [cellMeasure_zero_eq_cellVol, UnforcedLeray.B0581.cellVol]
      simp [Cyl.cellμ, Cyl.cell, UnforcedLeray.B0579.cell,
        show -(c / 2) = -c / 2 by ring]
    rw [hμ] at h0
    have hrep := houtMem.coeFn_toLp
    have hrep0 := (cellMeasure_ac_cellMeasure c 0 m).ae_le hrep
    rw [hμ] at hrep0
    filter_upwards [h0, hrep0] with z hz hr
    calc
      out z = (houtMem.toLp f : X c m) z := hz
      _ = f z := hr
  have hleftCell : xColumnHeatLift hc out =ᵐ[Cyl.cellμ c] (negativeHeatDiv θ T) := by
    filter_upwards [xColumnPeriodicRep_ae_eq hc out, hXc] with z hrep hout
    change (xColumnPeriodicRep hc out z, (0 : ℝ)) = negativeHeatDiv θ T z
    rw [hrep, hout]
    exact (Prod.ext rfl (negativeHeatDiv_scalarFluxTensor_snd hθ
      (xColumnPeriodicRep hc (F 0)) (xColumnPeriodicRep hc (F 1)) z).symm)
  have hleftPer : IsQPeriodic c (xColumnHeatLift hc out) := by
    intro z
    simpa [IsQPeriodic, Cyl.IsPeriodic, xColumnHeatLift] using
      periodic_xColumnHeatLift hc out z
  have hTper : IsQPeriodic c T := periodic_xFluxPeriodicTensor hc F
  have hrightPer : IsQPeriodic c (negativeHeatDiv θ T) := by
    intro z
    simp [negativeHeatDiv, B0296.heatDiv_periodic hTper z]
  have hcell := HeatCylinder.ae_eq_of_ae_centered_periodic hc
    hleftPer hrightPer hleftCell
  have hleft := coeFn_xColumnHeatInput hc hm out
  have hrightEq := Lp.ext_iff.mp (xFluxNegativeHeatDivL2CLM_eq_actual hc hm hθ F)
  let hTmem := memLp_xFluxPeriodicTensor_normalized hc hm F
  have hDivmem := HeatCylinder.periodicHeatDivMemLp hc hθ T hTper
    (measurable_xFluxPeriodicTensor hc F).aestronglyMeasurable hTmem
  have hTrep := hDivmem.coeFn_toLp
  have hneg : ((-(hDivmem.toLp (B0296.heatDiv θ T)) :
      Lp Plane 2 (B0284.cellMeasure c)) : Plane → Plane) =ᵐ[B0284.cellMeasure c]
      negativeHeatDiv θ T := by
    have hclass : ((hDivmem.toLp (B0296.heatDiv θ T) :
        Lp Plane 2 (B0284.cellMeasure c)) : Plane → Plane) =ᵐ[B0284.cellMeasure c]
        B0296.heatDiv θ T := hTrep
    filter_upwards [Lp.coeFn_neg (hDivmem.toLp (B0296.heatDiv θ T)), hclass] with z _hn ht
    change ((-(hDivmem.toLp (B0296.heatDiv θ T) :
      Lp Plane 2 (B0284.cellMeasure c)) : Lp Plane 2 (B0284.cellMeasure c)) z) =
      negativeHeatDiv θ T z
    rw [_hn]
    change -((hDivmem.toLp (B0296.heatDiv θ T) :
      Lp Plane 2 (B0284.cellMeasure c)) z) = negativeHeatDiv θ T z
    rw [ht]
    rfl
  apply Lp.ext
  filter_upwards [hleft, hcell, hrightEq, hneg] with z hl hcella hr hn
  calc
    (xColumnHeatInput hc hm out : Plane → Plane) z = xColumnHeatLift hc out z := hl
    _ = negativeHeatDiv θ T z := hcella
    _ = (xFluxNegativeHeatDivL2CLM hc hm hθ F : Plane → Plane) z := by
      simpa [T] using hn.symm.trans hr.symm

/-- The actual weighted positive S₀ output, when embedded in normalized-cell `L²`, is the
literal B0284 heat of the embedded input. This uses the established global representative
identity plus preservation of the zero second coordinate by the heat kernel. -/
theorem xColumnHeatInput_xColumnHeatS0Positive_eq_heatL2CLM {c m θ : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hm : 1 ≤ m) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (f : X c m) :
    xColumnHeatInput hc hm (xColumnHeatS0Positive hc hm hθ hθ1 f) =
      HeatCylinder.heatL2CLM hc θ (xColumnHeatInput hc hm f) := by
  let x := xColumnHeatInput hc hm f
  let y := HeatCylinder.heatL2CLM hc θ x
  let r := HeatCylinder.planeRep hc x
  let ry := HeatCylinder.planeRep hc y
  have hr := HeatCylinder.planeRep_spec hc x
  have hry := HeatCylinder.planeRep_spec hc y
  have hinput : r =ᵐ[B0284.cellMeasure c] xColumnHeatLift hc f :=
    hr.2.2.trans (coeFn_xColumnHeatInput hc hm f)
  have hinputGlobal : r =ᵐ[volume] xColumnHeatLift hc f := by
    apply B0289.ae_of_ae_cellMeasure hc
    · intro z
      apply propext
      constructor
      · intro hz
        calc
          r z = r (z.1 + c, z.2) := (hr.2.1 z).symm
          _ = xColumnHeatLift hc f (z.1 + c, z.2) := hz
          _ = xColumnHeatLift hc f z := periodic_xColumnHeatLift hc f z
      · intro hz
        calc
          r (z.1 + c, z.2) = r z := hr.2.1 z
          _ = xColumnHeatLift hc f z := hz
          _ = xColumnHeatLift hc f (z.1 + c, z.2) :=
            (periodic_xColumnHeatLift hc f z).symm
    · exact hinput
  have hYvalue : (y : Plane → Plane) =ᵐ[B0284.cellMeasure c]
      B0284.heat θ r := by
    let hmem := HeatCylinder.memLp_planeRep hc x
    have hheat : MemLp (B0284.heat θ r) 2 (B0284.cellMeasure c) := by
      refine ⟨B0296.aestronglyMeasurable_heat c θ hr.1.aestronglyMeasurable, ?_⟩
      have hcontract := B0284.eLpNorm_heat_le (θ := θ) hc hr.2.1
        hr.1.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        ENNReal.ofNat_ne_top
      exact lt_of_le_of_lt hcontract hmem.eLpNorm_ne_top.lt_top
    have hclass : HeatCylinder.heatL2 hc θ x = hheat.toLp (B0284.heat θ r) := by
      simp [HeatCylinder.heatL2, x, r, hheat]
    exact (Lp.ext_iff.mp hclass).trans hheat.coeFn_toLp
  have hheatCongr := B0289.heat_congr_ae hθ hinputGlobal
  have hsecond : (fun z => (ry z).2) =ᵐ[B0284.cellMeasure c] 0 := by
    filter_upwards [hry.2.2, hYvalue] with z hrep hy
    have hz : (B0284.heat θ (xColumnHeatLift hc f) z).2 = 0 :=
      heat_snd_eq_zero_of_snd_eq_zero hθ (xColumnHeatLift hc f)
        (fun z => rfl) z
    have hy' : (y z).2 = (B0284.heat θ r z).2 := congrArg Prod.snd hy
    have hrep' : (ry z).2 = (y z).2 := congrArg Prod.snd hrep
    have hheat := congrFun hheatCongr z
    rw [hrep', hy', hheat, hz]
    simp
  have houtRep := xColumnHeatS0Positive_periodicRep_eq_heatL2CLMRep
    hc hm hθ hθ1 f
  have houtCell : xColumnHeatLift hc (xColumnHeatS0Positive hc hm hθ hθ1 f) =ᵐ[
      B0284.cellMeasure c] ry := by
    have hfirst : (fun z =>
        (xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f) z)) =ᵐ[
          B0284.cellMeasure c] fun z => (ry z).1 :=
      (B0284.cellMeasure_ac c).ae_le houtRep
    filter_upwards [hfirst, hsecond] with z hfirst hsecond
    change (xColumnPeriodicRep hc (xColumnHeatS0Positive hc hm hθ hθ1 f) z, 0) = ry z
    exact Prod.ext hfirst hsecond.symm
  have hleft := coeFn_xColumnHeatInput hc hm
    (xColumnHeatS0Positive hc hm hθ hθ1 f)
  apply Lp.ext
  filter_upwards [hleft, houtCell, hry.2.2] with z hleft hout hrep
  calc
    (xColumnHeatInput hc hm (xColumnHeatS0Positive hc hm hθ hθ1 f) :
        Plane → Plane) z = xColumnHeatLift hc
          (xColumnHeatS0Positive hc hm hθ hθ1 f) z := hleft
    _ = ry z := hout
    _ = (y : Plane → Plane) z := hrep

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.negativeHeatDiv_scalarFluxTensor_snd
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatInput_xFluxNegativeHeatDivXCLM_eq
#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.xColumnHeatInput_xColumnHeatS0Positive_eq_heatL2CLM
