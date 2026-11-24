import UnforcedLeray.Lib.HeatCylinder.HeatVecH3Semigroup
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2ZeroAge
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3GraphContraction
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ActualValue

/-!
# Age-zero ordinary Gaussian heat on the smooth centered H³ core

The proof compares every ordered weak derivative with the normalized-cell vector Gaussian
orbit, then uses the exact centered/normalized period factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

private theorem heatVecConvolution_congr_ae_local {θ : ℝ} {f g : Plane → Vec}
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

/-- For a smooth periodic input, the quotient heat on any ordered derivative has the actual
Gaussian convolution as its normalized-cell representative. -/
theorem heatVecL2CLM_value_ae_iterD_cylSmooth {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    let Tα := UnforcedLeray.Sob.iterD vs T
    let hTα := hT.iterD vs
    let x := (memLp_iterD_vec_cylSmooth_normalized hc hT vs).toLp Tα
    (heatVecL2CLM hc θ x : Plane → Vec) =ᵐ[cellMeasure c]
      heatVecConvolution θ Tα := by
  dsimp only
  let Tα := UnforcedLeray.Sob.iterD vs T
  let hTα := hT.iterD vs
  let hm := memLp_iterD_vec_cylSmooth_normalized hc hT vs
  let x := hm.toLp Tα
  have hrepCell : normalizedVecHeatRep hc x =ᵐ[cellMeasure c] Tα := by
    filter_upwards [normalizedVecHeatRep_ae hc x, hm.coeFn_toLp] with z hrep hx
    exact hrep.trans hx
  have hperT : UnforcedLeray.B0284.IsQPeriodic c Tα := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hTα.periodic z
  have hrepVolume : normalizedVecHeatRep hc x =ᵐ[volume] Tα := by
    have hlift := perLift_congr_ae hc hrepCell
    have hleft := perLift_eq_self_of_periodic hc (normalizedVecHeatRep_periodic hc x)
    have hright := perLift_eq_self_of_periodic hc hperT
    filter_upwards [hlift] with z hz
    rw [congrFun hleft z, congrFun hright z] at hz
    exact hz
  have hrepPlane := normalizedVecHeatRep_eq_normalizedPlaneVecRep_ae hc x
  have hconvInput := heatVecConvolution_congr_ae_local (θ := θ) hrepVolume
  have hconvPlane := heatVecConvolution_congr_ae_local (θ := θ) hrepPlane.symm
  have hOut := heatVecL2CLM_value_ae hc hθ x
  filter_upwards [hOut] with z hz
  calc
    (heatVecL2CLM hc θ x : Plane → Vec) z =
        heatVecConvolution θ (fun q => UnforcedLeray.Train.toVec
          (planeRep hc ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL
            2 (cellMeasure c) x) q)) z := hz
    _ = heatVecConvolution θ (normalizedVecHeatRep hc x) z := congrFun hconvPlane z
    _ = heatVecConvolution θ Tα z := congrFun hconvInput z

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatVecL2CLM_value_ae_iterD_cylSmooth
