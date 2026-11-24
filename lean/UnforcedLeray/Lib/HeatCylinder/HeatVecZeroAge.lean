import UnforcedLeray.Lib.HeatCylinder.HeatVecTranslationNorm
import UnforcedLeray.Lib.HeatCylinder.HeatL2PlaneTranslation

/-!
# Continuity of the actual periodic translation modulus

This is the zero-age input estimate for the planar Gaussian approximate identity. Its normalized
cell `L²` modulus is exactly the centered translation modulus times `c^{-1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (cellMeasure)

noncomputable def heatVecCenteredInput {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) : UnforcedLeray.Cyl.L2v c :=
  centeredVecOfNormalizedPlane hc
    ((UnforcedLeray.Train.toVecL.symm : Vec →L[ℝ] Plane).compLpL 2 (cellMeasure c) x)

noncomputable def heatVecTranslationModulus {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) : ℝ :=
  Real.sqrt c⁻¹ * ‖planeShiftL2 hc w (heatVecCenteredInput hc x) -
    heatVecCenteredInput hc x‖

/-- The real normalized-cell translation modulus equals the square-root period factor times the
centered cylinder translation norm. -/
theorem eLpNorm_toReal_heatVecTranslationIncrement {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    (eLpNorm (fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z)
      2 (cellMeasure c)).toReal = heatVecTranslationModulus hc x w := by
  have hsq := eLpNorm_sq_heatVecTranslationIncrement hc x w
  have hcoef : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hnorm : 0 ≤ ‖planeShiftL2 hc w (heatVecCenteredInput hc x) -
      heatVecCenteredInput hc x‖ := norm_nonneg _
  have hrhs : 0 ≤ heatVecTranslationModulus hc x w :=
    mul_nonneg (Real.sqrt_nonneg _) hnorm
  have hsquares :
      heatVecTranslationModulus hc x w ^ 2 =
        c⁻¹ * ‖planeShiftL2 hc w (heatVecCenteredInput hc x) -
          heatVecCenteredInput hc x‖ ^ 2 := by
    rw [heatVecTranslationModulus, mul_pow, Real.sq_sqrt hcoef]
  apply (sq_eq_sq₀ ENNReal.toReal_nonneg hrhs).mp
  rw [hsquares]
  exact hsq

/-- The actual normalized-cell translation modulus tends to zero when its spatial shift tends
to zero. -/
theorem tendsto_heatVecTranslationModulus_zero {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) :
    Tendsto (fun w : Plane => heatVecTranslationModulus hc x w)
      (𝓝 (0 : Plane)) (𝓝 0) := by
  let y := heatVecCenteredInput hc x
  have hshift := tendsto_planeShiftL2_centered hc y
  have hconst : Tendsto (fun _ : Plane => y) (𝓝 (0 : Plane)) (𝓝 y) := tendsto_const_nhds
  have hdist := hshift.dist hconst
  have hnorm : Tendsto (fun w : Plane => ‖planeShiftL2 hc w y - y‖)
      (𝓝 (0 : Plane)) (𝓝 0) := by
    simpa only [dist_eq_norm, sub_self, norm_zero] using hdist
  simpa only [heatVecTranslationModulus, y, mul_zero] using
    (tendsto_const_nhds.mul hnorm)

/-- The `ENNReal` translation seminorm is the `ofReal` image of its finite real modulus. -/
theorem eLpNorm_heatVecTranslationIncrement_eq_ofReal {c : ℝ} (hc : 0 < c)
    (x : Lp Vec 2 (cellMeasure c)) (w : Plane) :
    eLpNorm (fun z => normalizedVecHeatRep hc x (z - w) - normalizedVecHeatRep hc x z)
      2 (cellMeasure c) = ENNReal.ofReal (heatVecTranslationModulus hc x w) := by
  rw [← ENNReal.ofReal_toReal
      (memLp_heatVecTranslationIncrement_normalized hc x w).eLpNorm_ne_top,
    eLpNorm_toReal_heatVecTranslationIncrement hc x w]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.eLpNorm_toReal_heatVecTranslationIncrement
#print axioms UnforcedLeray.HeatCylinder.tendsto_heatVecTranslationModulus_zero
#print axioms UnforcedLeray.HeatCylinder.eLpNorm_heatVecTranslationIncrement_eq_ofReal
