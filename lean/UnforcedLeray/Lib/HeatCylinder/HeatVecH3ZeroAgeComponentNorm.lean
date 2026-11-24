import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeNorm
import UnforcedLeray.Lib.HeatCylinder.CellBridge

/-!
# Period-normalized component norm identity for smooth H³ heat increments

The centered H³ weak derivative increment and its normalized-cell Gaussian L² increment have
squared norms related by exactly the period c.
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

private theorem heatVecH3_measure_eq_cell_local''' (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private theorem isQPeriodic_iterD_componentNorm {c : ℝ} {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
  intro z
  have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [hcoord]
  exact (hT.iterD vs).periodic z

/-- The exact centered versus normalized squared norm identity for one smooth H³ heat
increment derivative. -/
theorem norm_deriv_actualHeatVecH3_sub_ofCylSmooth_sq {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (α : UnforcedLeray.Sob.Idx 2 3) :
    ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
        (actualHeatVecH3CLM hc hθ
          (UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := Vec) (k := 3) (p := 2) hc T hT) -
          UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := Vec) (k := 3) (p := 2) hc T hT)‖ ^ 2 =
      c * ‖heatVecL2CLM hc θ
          ((memLp_iterD_vec_cylSmooth_normalized hc hT
            ((UnforcedLeray.Sob.cylinder c).word α)).toLp
              (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T)) -
        (memLp_iterD_vec_cylSmooth_normalized hc hT
          ((UnforcedLeray.Sob.cylinder c).word α)).toLp
            (UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) T)‖ ^ 2 := by
  rw [actualHeatVecH3CLM_apply_ofCylSmooth hc hθ hT]
  let vs := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD vs T
  let x := (memLp_iterD_vec_cylSmooth_normalized hc hT vs).toLp Tα
  let outField : Plane → Vec := heatVecH3Field (c := c) (θ := θ) T α
  let diffField : Plane → Vec := fun z => outField z - Tα z
  have hmeasOut : Measurable outField := by
    dsimp [outField, heatVecH3Field]
    exact (differentiable_heatVecConvolution_of_cylSmooth hc hθ (hT.iterD vs)).continuous.measurable
  have hperOut : UnforcedLeray.B0284.IsQPeriodic c outField := by
    dsimp [outField, heatVecH3Field]
    exact heatVecConvolution_periodic hc hθ (hT.iterD vs)
  have hmeasIn : Measurable Tα := (hT.iterD vs).smooth.continuous.measurable
  have hperIn : UnforcedLeray.B0284.IsQPeriodic c Tα :=
    isQPeriodic_iterD_componentNorm hT vs
  have hmeasDiff : Measurable diffField := hmeasOut.sub hmeasIn
  have hperDiff : UnforcedLeray.B0284.IsQPeriodic c diffField := by
    intro z
    dsimp [diffField]
    rw [hperOut z, hperIn z]
  have houtAE := deriv_heatVecH3_ae_cell hc hθ hT α
  have hinAE := deriv_ofCylSmooth_ae_cell hc hT α
  have hderivDiffAE :
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
        (heatVecH3 hc hθ hT - UnforcedLeray.Sob.W.ofCylSmooth
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := Vec) (k := 3) (p := 2) hc T hT) : Plane → Vec) =ᵐ[
            UnforcedLeray.Cyl.cellμ c] diffField := by
    have hmap := congrArg (fun f : Lp Vec 2
          (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
            (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) => (f : Plane → Vec))
        (map_sub (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α)
          (heatVecH3 hc hθ hT)
          (UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := Vec) (k := 3) (p := 2) hc T hT))
    have hsubW := Lp.coeFn_sub
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α (heatVecH3 hc hθ hT))
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
          (UnforcedLeray.Sob.W.ofCylSmooth
            (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
            (F := Vec) (k := 3) (p := 2) hc T hT))
    have hsubCell := by
      simpa only [heatVecH3_measure_eq_cell_local''' c] using hsubW
    filter_upwards [houtAE, hinAE, hsubCell] with z hout' hin' hsub'
    have hpoint := congrFun hmap z
    calc
      _ = _ := hpoint
      _ = _ := hsub'
      _ = outField z - Tα z := by rw [Pi.sub_apply, hout', hin']
      _ = diffField z := rfl
  have hderivDiffCell :
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
        (heatVecH3 hc hθ hT - UnforcedLeray.Sob.W.ofCylSmooth
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := Vec) (k := 3) (p := 2) hc T hT) : Plane → Vec) =ᵐ[
            UnforcedLeray.Cyl.cellμ c] diffField := hderivDiffAE
  have hcenterNorm :
      ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
        (heatVecH3 hc hθ hT - UnforcedLeray.Sob.W.ofCylSmooth
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := Vec) (k := 3) (p := 2) hc T hT)‖ =
      (eLpNorm diffField 2 (UnforcedLeray.Cyl.cellμ c)).toReal := by
    rw [Lp.norm_def]
    have hnorm := congrArg ENNReal.toReal
      (eLpNorm_congr_ae (p := 2) hderivDiffCell)
    simpa only [heatVecH3_measure_eq_cell_local''' c] using hnorm
  have hscale := eLpNorm_sq_cyl_eq_cellMeasure hc hmeasDiff hperDiff
  have hscaleReal := congrArg ENNReal.toReal hscale
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_of_lt hc), ENNReal.toReal_pow] at hscaleReal
  have houtNorm :
      eLpNorm diffField 2 (cellMeasure c) =
        eLpNorm (heatVecL2CLM hc θ x - x : Lp Vec 2 (cellMeasure c)) 2
          (cellMeasure c) := by
    have hOutAE := heatVecL2CLM_value_ae_iterD_cylSmooth hc hθ hT vs
    have hInAE := (memLp_iterD_vec_cylSmooth_normalized hc hT vs).coeFn_toLp
    have hDiffAE :
        ((heatVecL2CLM hc θ x - x : Lp Vec 2 (cellMeasure c)) : Plane → Vec) =ᵐ[
            cellMeasure c] diffField := by
      filter_upwards [Lp.coeFn_sub (heatVecL2CLM hc θ x) x, hOutAE, hInAE]
        with z hsub' hout' hin'
      dsimp [diffField, outField, heatVecH3Field, Tα, x, vs] at *
      calc
        ((heatVecL2CLM hc θ x - x : Lp Vec 2 (cellMeasure c)) : Plane → Vec) z =
            (heatVecL2CLM hc θ x : Plane → Vec) z - (x : Plane → Vec) z := hsub'
        _ = heatVecConvolution θ Tα z - Tα z := by rw [hout', hin']
        _ = diffField z := rfl
    exact eLpNorm_congr_ae hDiffAE.symm
  have hquotNorm :
      ‖heatVecL2CLM hc θ x - x‖ = (eLpNorm diffField 2 (cellMeasure c)).toReal := by
    rw [Lp.norm_def]
    rw [← houtNorm]
  change ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α
      (heatVecH3 hc hθ hT - UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT)‖ ^ 2 = _
  rw [hcenterNorm, hquotNorm]
  exact hscaleReal

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.norm_deriv_actualHeatVecH3_sub_ofCylSmooth_sq
