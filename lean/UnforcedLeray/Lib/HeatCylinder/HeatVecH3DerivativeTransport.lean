import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeNorm
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Density
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Operator
import UnforcedLeray.Lib.HeatCylinder.HeatL2NormalizedVecLinear

/-!
# Normalized L² realization of centered H³ derivatives

Every centered derivative class is sent to B0284's normalized cell by its actual centered
periodic representative. The exact measure conversion is retained in the map norm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)
open UnforcedLeray.Cyl (cellμ)

theorem heatVecH3_measure_eq_cell_deriv (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ, cellμ]

/-- A measurable representative of a centered-cell vector L² class. -/
noncomputable def centeredVecL2Rep {c : ℝ} (x : Lp Vec 2 (cellμ c)) : Plane → Vec :=
  (Lp.aestronglyMeasurable x).mk (x : Plane → Vec)

private theorem centeredVecL2Rep_measurable {c : ℝ} (x : Lp Vec 2 (cellμ c)) :
    Measurable (centeredVecL2Rep x) :=
  (Lp.aestronglyMeasurable x).measurable_mk

theorem centeredVecL2Rep_ae {c : ℝ} (x : Lp Vec 2 (cellμ c)) :
    centeredVecL2Rep x =ᵐ[cellμ c] (x : Plane → Vec) :=
  (Lp.aestronglyMeasurable x).ae_eq_mk.symm

/-- The actual centered periodic representative of a centered-cell vector L² class. -/
noncomputable def centeredVecL2PeriodicRep {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) : Plane → Vec :=
  centeredPerLift hc (centeredVecL2Rep x)

theorem measurable_centeredVecL2PeriodicRep {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) : Measurable (centeredVecL2PeriodicRep hc x) :=
  measurable_centeredPerLift hc (centeredVecL2Rep_measurable x)

theorem periodic_centeredVecL2PeriodicRep {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) : UnforcedLeray.B0284.IsQPeriodic c
      (centeredVecL2PeriodicRep hc x) := by
  intro z
  exact centeredPerLift_periodic hc _ z

theorem centeredVecL2PeriodicRep_ae_cell {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) :
    centeredVecL2PeriodicRep hc x =ᵐ[cellμ c] (x : Plane → Vec) := by
  filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c),
    centeredVecL2Rep_ae x] with z hz hrep
  change centeredPerLift hc (centeredVecL2Rep x) z = _
  rw [centeredPerLift_eq_on_cell hc _ hz]
  exact hrep

theorem memLp_centeredVecL2PeriodicRep_normalized {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) : MemLp (centeredVecL2PeriodicRep hc x) 2 (cellMeasure c) := by
  have hcenter : MemLp (centeredVecL2PeriodicRep hc x) 2 (cellμ c) :=
    (memLp_congr_ae (centeredVecL2PeriodicRep_ae_cell hc x)).mpr (Lp.memLp x)
  exact memLp_cellMeasure_of_memLp_cyl hc
    (measurable_centeredVecL2PeriodicRep hc x)
    (periodic_centeredVecL2PeriodicRep hc x) hcenter

/-- The actual centered-to-normalized quotient function, defined by centered periodic extension.
-/
noncomputable def centeredVecToNormalizedFun {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) : Lp Vec 2 (cellMeasure c) :=
  (memLp_centeredVecL2PeriodicRep_normalized hc x).toLp (centeredVecL2PeriodicRep hc x)

/-- The actual centered-to-normalized quotient transport, defined by centered periodic extension.
-/
noncomputable def centeredVecToNormalizedLinear {c : ℝ} (hc : 0 < c) :
    Lp Vec 2 (cellμ c) →ₗ[ℝ] Lp Vec 2 (cellMeasure c) where
  toFun := centeredVecToNormalizedFun hc
  map_add' x y := by
    have hx := memLp_centeredVecL2PeriodicRep_normalized hc x
    have hy := memLp_centeredVecL2PeriodicRep_normalized hc y
    have hxy := memLp_centeredVecL2PeriodicRep_normalized hc (x + y)
    have hbase : centeredVecL2Rep (x + y) =ᵐ[cellμ c]
        fun z => centeredVecL2Rep x z + centeredVecL2Rep y z := by
      filter_upwards [centeredVecL2Rep_ae (x + y), centeredVecL2Rep_ae x,
        centeredVecL2Rep_ae y, Lp.coeFn_add x y] with z hxy' hx' hy' hadd
      calc
        centeredVecL2Rep (x + y) z = (x + y : Lp Vec 2 (cellμ c)) z := hxy'
        _ = x z + y z := hadd
        _ = centeredVecL2Rep x z + centeredVecL2Rep y z := by rw [← hx', ← hy']
    have hperiodic := centeredPerLift_congr_ae hc hbase
    have hnorm : centeredVecL2PeriodicRep hc (x + y) =ᵐ[cellMeasure c]
        fun z => centeredVecL2PeriodicRep hc x z + centeredVecL2PeriodicRep hc y z := by
      apply ae_iff.mpr
      exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hperiodic)
    change hxy.toLp (centeredVecL2PeriodicRep hc (x + y)) =
      hx.toLp (centeredVecL2PeriodicRep hc x) + hy.toLp (centeredVecL2PeriodicRep hc y)
    rw [← MemLp.toLp_add hx hy]
    exact MemLp.toLp_congr hxy (hx.add hy) hnorm
  map_smul' r x := by
    apply Lp.ext
    have hbase : centeredVecL2Rep (r • x) =ᵐ[cellμ c]
        fun z => r • centeredVecL2Rep x z := by
      filter_upwards [centeredVecL2Rep_ae (r • x), centeredVecL2Rep_ae x,
        Lp.coeFn_smul r x] with z hrx hx hsmul
      calc
        centeredVecL2Rep (r • x) z = (r • x : Lp Vec 2 (cellμ c)) z := hrx
        _ = r • x z := hsmul
        _ = r • centeredVecL2Rep x z := by rw [← hx]
    have hperiodic := centeredPerLift_congr_ae hc hbase
    have hnorm : centeredVecL2PeriodicRep hc (r • x) =ᵐ[cellMeasure c]
        fun z => r • centeredVecL2PeriodicRep hc x z := by
      apply ae_iff.mpr
      exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hperiodic)
    filter_upwards [
      (memLp_centeredVecL2PeriodicRep_normalized hc (r • x)).coeFn_toLp,
      (memLp_centeredVecL2PeriodicRep_normalized hc x).coeFn_toLp,
      hnorm, Lp.coeFn_smul r (centeredVecToNormalizedFun hc x)] with
      z hsmul hx hrep hcoe
    change ((memLp_centeredVecL2PeriodicRep_normalized hc (r • x)).toLp
        (centeredVecL2PeriodicRep hc (r • x)) : Plane → Vec) z =
      (r • (memLp_centeredVecL2PeriodicRep_normalized hc x).toLp
          (centeredVecL2PeriodicRep hc x) : Lp Vec 2 (cellMeasure c)) z
    calc
      ((memLp_centeredVecL2PeriodicRep_normalized hc (r • x)).toLp
          (centeredVecL2PeriodicRep hc (r • x)) : Plane → Vec) z =
          centeredVecL2PeriodicRep hc (r • x) z := hsmul
      _ = r • centeredVecL2PeriodicRep hc x z := hrep
      _ = (r • (memLp_centeredVecL2PeriodicRep_normalized hc x).toLp
          (centeredVecL2PeriodicRep hc x) : Lp Vec 2 (cellMeasure c)) z := by
        rw [← hx]
        exact hcoe.symm

theorem centeredVecToNormalized_norm_sq {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) :
    ‖centeredVecToNormalizedLinear hc x‖ ^ 2 = c⁻¹ * ‖x‖ ^ 2 := by
  have hscale := eLpNorm_sq_cyl_eq_cellMeasure hc
    (measurable_centeredVecL2PeriodicRep hc x)
    (periodic_centeredVecL2PeriodicRep hc x)
  have hcenter : eLpNorm (x : Plane → Vec) 2 (cellμ c) =
      eLpNorm (centeredVecL2PeriodicRep hc x) 2 (cellμ c) :=
    eLpNorm_congr_ae (centeredVecL2PeriodicRep_ae_cell hc x).symm
  have hnormal : eLpNorm (centeredVecL2PeriodicRep hc x) 2 (cellMeasure c) =
      eLpNorm (centeredVecToNormalizedLinear hc x) 2 (cellMeasure c) := by
    exact (eLpNorm_congr_ae (p := (2 : ℝ≥0∞))
      (memLp_centeredVecL2PeriodicRep_normalized hc x).coeFn_toLp).symm
  have hreal := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt hc), ENNReal.toReal_pow] at hreal
  rw [← hcenter, hnormal] at hreal
  have hnormReal : ‖centeredVecToNormalizedFun hc x‖ ^ 2 =
      c⁻¹ * ‖x‖ ^ 2 := by
    have hreal' : ‖x‖ ^ 2 = c * ‖centeredVecToNormalizedLinear hc x‖ ^ 2 := by
      simpa only [Lp.norm_def, centeredVecToNormalizedLinear,
        centeredVecToNormalizedFun] using hreal
    have hcne : c ≠ 0 := ne_of_gt hc
    calc
      ‖centeredVecToNormalizedLinear hc x‖ ^ 2 =
          c⁻¹ * (c * ‖centeredVecToNormalizedLinear hc x‖ ^ 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
      _ = c⁻¹ * ‖x‖ ^ 2 := by rw [← hreal']
  change ‖centeredVecToNormalizedFun hc x‖ ^ 2 = c⁻¹ * ‖x‖ ^ 2
  simpa only [Lp.norm_def] using hnormReal


/-- Continuous centered-to-normalized L² transport, with the exact square-root cell factor. -/
noncomputable def centeredVecToNormalizedCLM {c : ℝ} (hc : 0 < c) :
    Lp Vec 2 (cellμ c) →L[ℝ] Lp Vec 2 (cellMeasure c) :=
  (centeredVecToNormalizedLinear hc).mkContinuous (Real.sqrt c⁻¹) (by
    intro x
    have hsq := centeredVecToNormalized_norm_sq hc x
    have hsqrt : (Real.sqrt c⁻¹) ^ 2 = c⁻¹ :=
      Real.sq_sqrt (inv_nonneg.mpr hc.le)
    have heq : ‖centeredVecToNormalizedLinear hc x‖ ^ 2 =
        (Real.sqrt c⁻¹ * ‖x‖) ^ 2 := by
      calc
        ‖centeredVecToNormalizedLinear hc x‖ ^ 2 = c⁻¹ * ‖x‖ ^ 2 := hsq
        _ = (Real.sqrt c⁻¹ * ‖x‖) ^ 2 := by rw [mul_pow, hsqrt]
    have hnonneg₁ := norm_nonneg (centeredVecToNormalizedLinear hc x)
    have hnonneg₂ := mul_nonneg (Real.sqrt_nonneg (c⁻¹)) (norm_nonneg x)
    nlinarith)

/-- Centered-to-normalized transport is a left inverse to periodic realization of normalized data.
-/
theorem centeredVecToNormalizedLinear_centeredVecOfNormalizedVec {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    centeredVecToNormalizedLinear hc (centeredVecOfNormalizedVec hc x) = x := by
  have hbase : centeredVecL2Rep (centeredVecOfNormalizedVec hc x) =ᵐ[cellμ c]
      normalizedVecPeriodicRep hc x :=
    (centeredVecL2Rep_ae (centeredVecOfNormalizedVec hc x)).trans
      (centeredVecOfNormalizedVec_coe_ae hc x)
  have hlift := centeredPerLift_congr_ae hc hbase
  have hself := centeredPerLift_eq_self_of_periodic hc
    (normalizedVecPeriodicRep_periodic hc x)
  have hvol : centeredVecL2PeriodicRep hc (centeredVecOfNormalizedVec hc x) =ᵐ[volume]
      normalizedVecPeriodicRep hc x := by
    filter_upwards [hlift] with z hz
    exact hz.trans (congrFun hself z)
  have hleftCell : centeredVecL2PeriodicRep hc (centeredVecOfNormalizedVec hc x) =ᵐ[cellMeasure c]
      normalizedVecPeriodicRep hc x := by
    apply ae_iff.mpr
    exact (UnforcedLeray.B0284.cellMeasure_ac c) (ae_iff.mp hvol)
  have hcell := hleftCell.trans (normalizedVecPeriodicRep_cell_ae hc x)
  change (memLp_centeredVecL2PeriodicRep_normalized hc
      (centeredVecOfNormalizedVec hc x)).toLp
      (centeredVecL2PeriodicRep hc (centeredVecOfNormalizedVec hc x)) = x
  exact (MemLp.toLp_congr
    (memLp_centeredVecL2PeriodicRep_normalized hc (centeredVecOfNormalizedVec hc x))
    (Lp.memLp x) hcell).trans (Lp.toLp_coeFn x (Lp.memLp x))

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.centeredVecToNormalizedLinear
#print axioms UnforcedLeray.HeatCylinder.centeredVecToNormalized_norm_sq
#print axioms UnforcedLeray.HeatCylinder.centeredVecToNormalizedLinear_centeredVecOfNormalizedVec
#print axioms UnforcedLeray.HeatCylinder.centeredVecToNormalizedCLM
