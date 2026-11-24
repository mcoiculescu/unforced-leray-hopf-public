import UnforcedLeray.Lib.HeatCylinder.P0PlaneShift
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeTransport
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2

/-!
# Centered heat/P₀ compatibility from the actual Gaussian translation average

This file factors the projection step through the centered-cell quotient. The average identity is
kept as an explicit premise until the periodic-cell Bochner representation is proved; it is not
silently assumed as a property of B0284 heat.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (L2v)
open UnforcedLeray.B0284 (cellMeasure heatKernel2)

/-- The full planar translation as a continuous linear map on centered-cell vector `L²`. -/
noncomputable def planeShiftL2CLM {c : ℝ} (hc : 0 < c) (w : Plane) :
    L2v c →L[ℝ] L2v c :=
  ((UnforcedLeray.TrainB.qShiftL2Isometry hc (-w.1)).toContinuousLinearMap).comp
    ((UnforcedLeray.TrainB.etaShiftL2 c (-w.2)).toContinuousLinearMap)

@[simp] theorem planeShiftL2CLM_apply {c : ℝ} (hc : 0 < c) (w : Plane) (x : L2v c) :
    planeShiftL2CLM hc w x = planeShiftL2 hc w x := rfl

/-- The actual normalized B0284 heat, transported to centered-cell vector `L²` by the inverse
periodic quotient maps. -/
noncomputable def centeredHeatVecL2CLM {c : ℝ} (hc : 0 < c) (θ : ℝ) :
    L2v c →L[ℝ] L2v c :=
  (normalizedVecToCenteredCLM hc).comp
    ((heatVecL2CLM hc θ).comp (centeredVecToNormalizedCLM hc))

/-- The centered-to-normalized vector transport has the exact square-root measure factor. -/
theorem norm_centeredVecToNormalizedCLM_le {c : ℝ} (hc : 0 < c) :
    ‖centeredVecToNormalizedCLM hc‖ ≤ Real.sqrt c⁻¹ := by
  exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _)
    (by
      intro x
      change ‖centeredVecToNormalizedLinear hc x‖ ≤ Real.sqrt c⁻¹ * ‖x‖
      have hsq := centeredVecToNormalized_norm_sq hc x
      have hsqrt : (Real.sqrt c⁻¹) ^ 2 = c⁻¹ := Real.sq_sqrt (inv_nonneg.mpr hc.le)
      have heq : ‖centeredVecToNormalizedLinear hc x‖ ^ 2 =
          (Real.sqrt c⁻¹ * ‖x‖) ^ 2 := by
        calc
          ‖centeredVecToNormalizedLinear hc x‖ ^ 2 = c⁻¹ * ‖x‖ ^ 2 := hsq
          _ = (Real.sqrt c⁻¹ * ‖x‖) ^ 2 := by rw [mul_pow, hsqrt]
      nlinarith [norm_nonneg (centeredVecToNormalizedLinear hc x),
        mul_nonneg (Real.sqrt_nonneg (c⁻¹)) (norm_nonneg x)])

/-- The actual centered-cell heat CLM is contractive: the `√c` and `√(c⁻¹)` quotient factors
cancel around the normalized-cell Gaussian contraction. -/
theorem norm_centeredHeatVecL2CLM_le_one {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    ‖centeredHeatVecL2CLM hc θ‖ ≤ 1 := by
  have hA : ‖normalizedVecToCenteredCLM hc‖ ≤ Real.sqrt c :=
    norm_normalizedVecToCenteredCLM_le hc
  have hH : ‖heatVecL2CLM hc θ‖ ≤ 1 := norm_heatVecL2CLM_le_one_of_pos hc hθ
  have hC : ‖centeredVecToNormalizedCLM hc‖ ≤ Real.sqrt c⁻¹ :=
    norm_centeredVecToNormalizedCLM_le hc
  have hprod : ‖centeredHeatVecL2CLM hc θ‖ ≤
      ‖normalizedVecToCenteredCLM hc‖ * ‖heatVecL2CLM hc θ‖ *
        ‖centeredVecToNormalizedCLM hc‖ := by
    change ‖(normalizedVecToCenteredCLM hc).comp
      ((heatVecL2CLM hc θ).comp (centeredVecToNormalizedCLM hc))‖ ≤ _
    calc
      _ ≤ ‖normalizedVecToCenteredCLM hc‖ *
          ‖(heatVecL2CLM hc θ).comp (centeredVecToNormalizedCLM hc)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖normalizedVecToCenteredCLM hc‖ *
          (‖heatVecL2CLM hc θ‖ * ‖centeredVecToNormalizedCLM hc‖) := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le (heatVecL2CLM hc θ)
            (centeredVecToNormalizedCLM hc))
          (norm_nonneg (normalizedVecToCenteredCLM hc))
      _ = ‖normalizedVecToCenteredCLM hc‖ * ‖heatVecL2CLM hc θ‖ *
          ‖centeredVecToNormalizedCLM hc‖ := by ring
  have hsqrt : Real.sqrt c * Real.sqrt c⁻¹ = 1 := by
    have hsq : (Real.sqrt c * Real.sqrt c⁻¹) ^ 2 = 1 := by
      rw [mul_pow, Real.sq_sqrt hc.le,
        Real.sq_sqrt (inv_nonneg.mpr hc.le)]
      field_simp
    nlinarith [mul_nonneg (Real.sqrt_nonneg c) (Real.sqrt_nonneg (c⁻¹))]
  calc
    ‖centeredHeatVecL2CLM hc θ‖ ≤
        ‖normalizedVecToCenteredCLM hc‖ * ‖heatVecL2CLM hc θ‖ *
          ‖centeredVecToNormalizedCLM hc‖ := hprod
    _ ≤ Real.sqrt c * 1 * Real.sqrt c⁻¹ := by
      gcongr
    _ = 1 := by rw [mul_one, hsqrt]

/-- If the actual centered heat is represented by the Gaussian Bochner average of its actual
planar translations, then the centered Leray projection commutes with it. The remaining analytic
obligation is precisely to prove `havg` for the periodic cell measure. -/
theorem centeredHeatVecL2CLM_P0_comm_of_gaussianAverage {c θ : ℝ} (hc : 0 < c)
    (_hθ : 0 < θ)
    (havg : ∀ x : L2v c,
      centeredHeatVecL2CLM hc θ x =
        ∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w x)
    (hint : ∀ x : L2v c,
      Integrable (fun w : Plane => heatKernel2 θ w • planeShiftL2CLM hc w x))
    (x : L2v c) :
    centeredHeatVecL2CLM hc θ (UnforcedLeray.Cyl.P0 c x) =
      UnforcedLeray.Cyl.P0 c (centeredHeatVecL2CLM hc θ x) := by
  calc
    centeredHeatVecL2CLM hc θ (UnforcedLeray.Cyl.P0 c x) =
        ∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w
          (UnforcedLeray.Cyl.P0 c x) := havg _
    _ = ∫ w : Plane, (UnforcedLeray.Cyl.P0 c)
          (heatKernel2 θ w • planeShiftL2CLM hc w x) := by
        congr 1
        funext w
        rw [map_smul]
        change heatKernel2 θ w • planeShiftL2 hc w (UnforcedLeray.Cyl.P0 c x) = _
        rw [planeShiftL2_P0_comm hc w x, planeShiftL2CLM_apply]
    _ = (UnforcedLeray.Cyl.P0 c)
          (∫ w : Plane, heatKernel2 θ w • planeShiftL2CLM hc w x) :=
        (UnforcedLeray.Cyl.P0 c).integral_comp_comm (hint x)
    _ = UnforcedLeray.Cyl.P0 c (centeredHeatVecL2CLM hc θ x) := by
        rw [(havg x).symm]

#print axioms UnforcedLeray.HeatCylinder.planeShiftL2CLM
#print axioms UnforcedLeray.HeatCylinder.centeredHeatVecL2CLM
#print axioms UnforcedLeray.HeatCylinder.norm_centeredVecToNormalizedCLM_le
#print axioms UnforcedLeray.HeatCylinder.norm_centeredHeatVecL2CLM_le_one
#print axioms UnforcedLeray.HeatCylinder.centeredHeatVecL2CLM_P0_comm_of_gaussianAverage

end UnforcedLeray.HeatCylinder
