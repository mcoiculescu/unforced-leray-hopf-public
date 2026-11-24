import UnforcedLeray.Lib.TrainB.DatumHeatBounds
import UnforcedLeray.Lib.HeatCylinder.HeatVecGeneralDerivative

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- Every ordered derivative of the actual periodized Gaussian Train datum commutes through the
literal positive-age Euclidean-vector heat convolution. The bounds needed for differentiating the
Gaussian integral are supplied by the actual uniform Fréchet-jet estimates `Train.datum_bounds`. -/
theorem datum_iterD_heatVecConvolution_commute {c θ : ℝ} (hc : 2 ≤ c) (hθ : 0 < θ)
    (vs : List Plane) :
    Sob.iterD vs (HeatCylinder.heatVecConvolution θ (Train.datum c)) =
      HeatCylinder.heatVecConvolution θ (Sob.iterD vs (Train.datum c)) := by
  apply HeatCylinder.iterD_heatVecConvolution_commute_of_bounds hθ
    (Train.datum_contDiff (by linarith))
  · intro ws
    exact datum_iterD_global_bound hc ws
  · intro ws
    exact datum_fderiv_iterD_global_bound hc ws

#print axioms UnforcedLeray.TrainB.datum_iterD_heatVecConvolution_commute

end UnforcedLeray.TrainB
