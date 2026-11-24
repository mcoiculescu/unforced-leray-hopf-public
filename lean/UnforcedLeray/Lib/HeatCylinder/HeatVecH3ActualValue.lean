import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Density
import UnforcedLeray.Lib.HeatCylinder.HeatVecActualContraction
import UnforcedLeray.Lib.HeatCylinder.H3ValueLimit
import UnforcedLeray.Lib.HeatCylinder.HeatVecTranslationBridge
import UnforcedLeray.Lib.HeatCylinder.HeatVecTranslationNorm

/-!
# Actual normalized L² value of smooth ordinary H³ heat

The smooth H³ construction is identified with the existing quotient-valued Gaussian heat CLM.
This is the value compatibility needed to extend it by completion, not a separately postulated
semigroup action.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem h3VecMeasure_eq_cell_heat (c : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c := by
  rw [UnforcedLeray.Cyl.wμ_ρwW]
  simp [UnforcedLeray.Cyl.wμ]

private theorem isQPeriodic_iterD_vecValue {c : ℝ} {T : Plane → Vec}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    UnforcedLeray.B0284.IsQPeriodic c (UnforcedLeray.Sob.iterD vs T) := by
  intro z
  have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
  rw [hcoord]
  exact (hT.iterD vs).periodic z

/-- The normalized periodic value map recovers the actual smooth input L² class. -/
theorem vectorH3NormalizedValue_ofCylSmoothVec {c : ℝ} (hc : 0 < c)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    vectorH3NormalizedValue hc
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT) =
      (memLp_iterD_vec_cylSmooth_normalized hc hT []).toLp T := by
  let y := UnforcedLeray.Sob.W.ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc T hT
  have hval := UnforcedLeray.Sob.W.value_ofCylSmooth
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Vec) (k := 3) (p := 2) hc T hT
  have hvalCell :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y : Plane → Vec) =ᵐ[
          UnforcedLeray.Cyl.cellμ c] T := by
    simpa only [h3VecMeasure_eq_cell_heat c, y] using hval
  have hcenter : vectorH3PeriodicValueRep hc y =ᵐ[UnforcedLeray.Cyl.cellμ c] T := by
    filter_upwards [vectorH3PeriodicValueRep_ae_value hc y, hvalCell] with z hrep hvalue
    exact hrep.trans hvalue
  have hglobal := ae_eq_of_ae_centered_periodic hc
    (periodic_vectorH3PeriodicValueRep hc y) (isQPeriodic_iterD_vecValue hT []) hcenter
  apply Lp.ext
  filter_upwards [vectorH3NormalizedValue_coe_ae hc y,
    (memLp_iterD_vec_cylSmooth_normalized hc hT []).coeFn_toLp,
    hglobal] with z hleft hright hrep
  exact hleft.trans (hrep.trans hright.symm)

private theorem heatVecConvolution_congr_ae {θ : ℝ} {f g : Plane → Vec}
    (hfg : f =ᵐ[volume] g) : heatVecConvolution θ f = heatVecConvolution θ g := by
  funext z
  unfold heatVecConvolution
  have hmap : MeasurePreserving (fun w : Plane => -w + z) volume volume :=
    (measurePreserving_add_right volume z).comp (Measure.measurePreserving_neg volume)
  have hshift : (fun w : Plane => f (z - w)) =ᵐ[volume] fun w => g (z - w) := by
    have h := hmap.quasiMeasurePreserving.ae hfg
    filter_upwards [h] with w hw
    simpa only [sub_eq_add_neg, add_comm] using hw
  apply integral_congr_ae
  filter_upwards [hshift] with w hw
  simp [hw]

/-- On a smooth compact-axial periodic vector field, the actual H³ heat output's normalized value
is the actual quotient-valued Gaussian heat operator on the input's normalized H³ value. -/
theorem vectorH3NormalizedValue_heatVecH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    vectorH3NormalizedValue hc (heatVecH3 hc hθ hT) =
      heatVecL2CLM hc θ (vectorH3NormalizedValue hc
        (UnforcedLeray.Sob.W.ofCylSmooth
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
          (F := Vec) (k := 3) (p := 2) hc T hT)) := by
  let hm := memLp_iterD_vec_cylSmooth_normalized hc hT []
  let x := hm.toLp T
  have hinput : vectorH3NormalizedValue hc
      (UnforcedLeray.Sob.W.ofCylSmooth
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
        (F := Vec) (k := 3) (p := 2) hc T hT) = x :=
    vectorH3NormalizedValue_ofCylSmoothVec hc hT
  have hrepCell : normalizedVecHeatRep hc x =ᵐ[UnforcedLeray.B0284.cellMeasure c] T := by
    filter_upwards [normalizedVecHeatRep_ae hc x, hm.coeFn_toLp] with z hrep hx
    exact hrep.trans hx
  have hrepVolume : normalizedVecHeatRep hc x =ᵐ[volume] T := by
    have hperT : UnforcedLeray.B0284.IsQPeriodic c T := by
      simpa only [UnforcedLeray.Sob.iterD_nil] using isQPeriodic_iterD_vecValue hT []
    have hlift := perLift_congr_ae hc hrepCell
    have hleft := perLift_eq_self_of_periodic hc
      (normalizedVecHeatRep_periodic hc x)
    have hright := perLift_eq_self_of_periodic hc hperT
    filter_upwards [hlift] with z hz
    rw [congrFun hleft z, congrFun hright z] at hz
    exact hz
  have hconv : heatVecConvolution θ (normalizedVecHeatRep hc x) =
      heatVecConvolution θ T := heatVecConvolution_congr_ae hrepVolume
  have hOut := heatVecL2CLM_value_ae hc hθ x
  have hplaneRep := normalizedVecHeatRep_eq_normalizedPlaneVecRep_ae hc x
  have hconvPlane := heatVecConvolution_congr_ae (θ := θ) hplaneRep.symm
  have hOutT : (heatVecL2CLM hc θ x : Plane → Vec) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] heatVecConvolution θ T := by
    filter_upwards [hOut] with z hout
    calc
      ((heatVecL2CLM hc θ x : Plane → Vec) z) =
          heatVecConvolution θ
            (fun q => UnforcedLeray.Train.toVec
              (planeRep hc ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
                2 (UnforcedLeray.B0284.cellMeasure c) x) q)) z := hout
      _ = heatVecConvolution θ (normalizedVecHeatRep hc x) z := congrFun hconvPlane z
      _ = heatVecConvolution θ T z := congrFun hconv z
  have hval := heatVecH3_value_ae hc hθ hT
  have hvalCell :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2
          (heatVecH3 hc hθ hT) : Plane → Vec) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        heatVecConvolution θ T := by
    simpa only [h3VecMeasure_eq_cell_heat c] using hval
  have hcenter : vectorH3PeriodicValueRep hc (heatVecH3 hc hθ hT) =ᵐ[
      UnforcedLeray.Cyl.cellμ c] heatVecConvolution θ T := by
    filter_upwards [vectorH3PeriodicValueRep_ae_value hc (heatVecH3 hc hθ hT),
      hvalCell] with z hrep hvalue
    exact hrep.trans hvalue
  have hglobal := ae_eq_of_ae_centered_periodic hc
    (periodic_vectorH3PeriodicValueRep hc (heatVecH3 hc hθ hT))
    (heatVecConvolution_periodic hc hθ hT) hcenter
  have hglobalCell : vectorH3PeriodicValueRep hc (heatVecH3 hc hθ hT) =ᵐ[
      UnforcedLeray.B0284.cellMeasure c] heatVecConvolution θ T := hglobal
  rw [hinput]
  apply Lp.ext
  filter_upwards [vectorH3NormalizedValue_coe_ae hc (heatVecH3 hc hθ hT),
    hOutT, hglobalCell] with z hleft hright hper
  exact hleft.trans (hper.trans hright.symm)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue_ofCylSmoothVec
#print axioms UnforcedLeray.HeatCylinder.vectorH3NormalizedValue_heatVecH3
