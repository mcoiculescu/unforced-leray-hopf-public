import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeSmooth
import UnforcedLeray.Lib.HeatCylinder.HeatL2NormalizedVecLinear

/-!
# Centered components of the smooth ordinary heat orbit

For each ordered derivative, the centered H³ component is the periodic centered realization of
its actual normalized-cell Gaussian L² orbit.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

private theorem heatVecH3_measure_eq_cell_local (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private theorem isQPeriodic_iterD_local {c : ℝ} {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
  intro z
  have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [hcoord]
  exact (hT.iterD vs).periodic z

private theorem memLp_heatVecH3Field_centered_local {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (α : UnforcedLeray.Sob.Idx 2 3) :
    MemLp (heatVecH3Field (c := c) (θ := θ) T α) 2
      (UnforcedLeray.Cyl.cellμ c) := by
  have hfield := memLp_heatVecH3Field hc hθ hT α
  simpa only [heatVecH3_measure_eq_cell_local c] using hfield

/-- The normalized heat of a smooth derivative, periodically extended to the centered cell, is
exactly the actual Gaussian field used in the H³ heat output. -/
theorem centeredVecOfNormalizedVec_heatVecL2CLM_iterD {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (α : UnforcedLeray.Sob.Idx 2 3) :
    centeredVecOfNormalizedVec hc
      (heatVecL2CLM hc θ
        ((memLp_iterD_vec_cylSmooth_normalized hc hT
          ((UnforcedLeray.Sob.cylinder c).word α)).toLp
          (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T))) =
    (memLp_heatVecH3Field_centered_local hc hθ hT α).toLp
      (heatVecH3Field (c := c) (θ := θ) T α) := by
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD vs T
  let hm := memLp_iterD_vec_cylSmooth_normalized hc hT vs
  let x := hm.toLp Tα
  have hperT : UnforcedLeray.B0284.IsQPeriodic c Tα := isQPeriodic_iterD_local hT vs
  have hrepCell : normalizedVecPeriodicRep hc
      (heatVecL2CLM hc θ x) =ᵐ[cellMeasure c] heatVecConvolution θ Tα := by
    exact (normalizedVecPeriodicRep_cell_ae hc (heatVecL2CLM hc θ x)).trans
      (heatVecL2CLM_value_ae_iterD_cylSmooth hc hθ hT vs)
  have hperConv : UnforcedLeray.B0284.IsQPeriodic c (heatVecConvolution θ Tα) := by
    exact heatVecConvolution_periodic hc hθ (hT.iterD vs)
  have hrepVolume : normalizedVecPeriodicRep hc (heatVecL2CLM hc θ x) =ᵐ[volume]
      heatVecConvolution θ Tα := by
    have hlift := perLift_congr_ae hc hrepCell
    have hleft := perLift_eq_self_of_periodic hc
      (normalizedVecPeriodicRep_periodic hc (heatVecL2CLM hc θ x))
    have hright := perLift_eq_self_of_periodic hc hperConv
    filter_upwards [hlift] with z hz
    rw [congrFun hleft z, congrFun hright z] at hz
    exact hz
  have hcenter : normalizedVecPeriodicRep hc (heatVecL2CLM hc θ x) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] heatVecConvolution θ Tα :=
    ae_restrict_of_ae (s := UnforcedLeray.Cyl.cell c) hrepVolume
  have hfieldCell := memLp_heatVecH3Field_centered_local hc hθ hT α
  have hout := hfieldCell.coeFn_toLp
  have hfieldConv : heatVecH3Field (c := c) (θ := θ) T α =
      heatVecConvolution θ Tα := by rfl
  have houtCell : (hfieldCell.toLp (heatVecH3Field (c := c) (θ := θ) T α) : Plane → Vec) =ᵐ[
        UnforcedLeray.Cyl.cellμ c] heatVecConvolution θ Tα := by
    filter_upwards [hout] with z hz
    simpa only [hfieldConv] using hz
  apply Lp.ext
  filter_upwards [centeredVecOfNormalizedVec_coe_ae hc (heatVecL2CLM hc θ x),
    hcenter, houtCell] with z hrep hconv hout
  exact hrep.trans (hconv.trans hout.symm)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.centeredVecOfNormalizedVec_heatVecL2CLM_iterD
