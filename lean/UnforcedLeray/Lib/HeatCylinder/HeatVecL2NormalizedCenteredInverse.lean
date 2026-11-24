import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeTransport
import UnforcedLeray.Lib.HeatCylinder.HeatVecTranslationBridge

/-!
# The reverse identity for the centered/normalized vector L² quotient transports

The two cell conventions are connected by actual periodic representatives. This proves that
periodizing a centered class and restricting it back to the centered cell recovers the original
quotient class.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)
open UnforcedLeray.Cyl (cellμ)

/-- Normalizing a centered vector class and periodically extending it back is the identity. -/
theorem normalizedVecToCenteredLinear_centeredVecToNormalizedLinear {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellμ c)) :
    normalizedVecToCenteredLinear hc (centeredVecToNormalizedLinear hc x) = x := by
  let y := centeredVecToNormalizedLinear hc x
  have hyrep : normalizedVecRep y =ᵐ[cellMeasure c]
      centeredVecL2PeriodicRep hc x := by
    exact (normalizedVecRep_ae y).trans
      (memLp_centeredVecL2PeriodicRep_normalized hc x).coeFn_toLp
  have hper : UnforcedLeray.B0284.IsQPeriodic c (centeredVecL2PeriodicRep hc x) := by
    intro z
    exact periodic_centeredVecL2PeriodicRep hc x z
  have hself := perLift_eq_self_of_periodic hc hper
  have hglobal : normalizedVecPeriodicRep hc y =ᵐ[volume]
      centeredVecL2PeriodicRep hc x := by
    filter_upwards [perLift_congr_ae hc hyrep] with z hz
    exact hz.trans (congrFun hself z)
  apply Lp.ext
  filter_upwards [centeredVecOfNormalizedVec_coe_ae hc y,
    ae_restrict_of_ae (s := UnforcedLeray.Cyl.cell c) hglobal,
    centeredVecL2PeriodicRep_ae_cell hc x] with z hcenter hglobal hx
  calc
    (centeredVecOfNormalizedVec hc y : Plane → Vec) z =
        normalizedVecPeriodicRep hc y z := hcenter
    _ = centeredVecL2PeriodicRep hc x z := hglobal
    _ = (x : Plane → Vec) z := hx

#print axioms UnforcedLeray.HeatCylinder.normalizedVecToCenteredLinear_centeredVecToNormalizedLinear

end UnforcedLeray.HeatCylinder
