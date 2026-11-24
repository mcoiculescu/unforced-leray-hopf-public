import UnforcedLeray.Analysis.ViscosityTransport.TestCalculus
import UnforcedLeray.Analysis.DerivativeScaling

/-!
# Exact weak-pairing formulas for spatial viscosity normalization

These pointwise identities use the actual Fréchet derivatives in the weak
momentum equation. They identify the common coefficient of all four terms
when the amplitude and spatial scale obey the viscosity normalization rules.
-/

noncomputable section
open Set MeasureTheory
open UnforcedLeray.SpatialScaling
namespace UnforcedLeray.ViscosityTransport

@[simp] theorem pullbackTest_at_dilation (b : ℝ) (hb : b ≠ 0)
    (φ : SpaceTime → Space) (t : ℝ) (x : Space) :
    pullbackTest b φ (t, b • x) = φ (t, x) := by
  simp only [pullbackTest, inv_smul_smul₀ hb]

theorem temporalTerm_scale (a b : ℝ) (hb : b ≠ 0)
    (u : Velocity) (φ : SpaceTime → Space) (z : SpaceTime) :
    temporalTerm (scaleVelocity a b u) φ z =
      a * temporalTerm u (pullbackTest b φ) (spaceMap b z) := by
  simp only [temporalTerm, scaleVelocity, spaceMap,
    timeDerivative_pullback_at_dilation b hb, real_inner_smul_left]

theorem convectionTerm_scale (a b : ℝ) (hb : b ≠ 0)
    (u : Velocity) (φ : SpaceTime → Space) (z : SpaceTime) :
    convectionTerm (scaleVelocity a b u) φ z =
      (a ^ 2 * b) * convectionTerm u (pullbackTest b φ) (spaceMap b z) := by
  simp only [convectionTerm, scaleVelocity, spaceMap,
    spatialDerivative_pullback_at_dilation b hb, ContinuousLinearMap.map_smul,
    smul_apply, real_inner_smul_left, real_inner_smul_right]
  field_simp

theorem diffusionTerm_scale (a b : ℝ) (hb : b ≠ 0)
    (u : Velocity) (φ : SpaceTime → Space) (z : SpaceTime) :
    diffusionTerm (scaleVelocity a b u) φ z =
      (a * b ^ 2) * diffusionTerm u (pullbackTest b φ) (spaceMap b z) := by
  simp only [diffusionTerm, scaleVelocity, spaceMap,
    spatialLaplacian_pullback_at_dilation b hb,
    real_inner_smul_left, real_inner_smul_right]
  field_simp

theorem pressureTerm_scale (c b : ℝ) (hb : b ≠ 0)
    (p : Pressure) (φ : SpaceTime → Space) (z : SpaceTime) :
    pressureTerm (scalePressure c b p) φ z =
      (c * b) * pressureTerm p (pullbackTest b φ) (spaceMap b z) := by
  simp only [pressureTerm, scalePressure, spaceMap,
    spatialDivergence_pullback_at_dilation b hb]
  field_simp

/-- Initial-data pairing transforms with precisely the temporal coefficient. -/
theorem datumPairing_scale (a b : ℝ) (hb : b ≠ 0)
    (u₀ : SpatialField) (φ : SpaceTime → Space) (x : Space) :
    inner ℝ (spatialScale a b u₀ x) (φ (0, x)) =
      a * inner ℝ (u₀ (b • x)) (pullbackTest b φ (0, b • x)) := by
  simp only [spatialScale, pullbackTest_at_dilation b hb, real_inner_smul_left]

/-- All four momentum terms acquire the same amplitude when the spatial
scale is the square root of the old viscosity. -/
theorem weakIntegrand_scale (a b c ν : ℝ) (hb : b ≠ 0)
    (hab : a * b = 1) (hbν : b ^ 2 = ν) (hcb : c * b = a)
    (u : Velocity) (p : Pressure) (φ : SpaceTime → Space) (z : SpaceTime) :
    weakIntegrand (scaleVelocity a b u) (scalePressure c b p) φ z =
      a * viscosityWeakIntegrand ν u p (pullbackTest b φ) (spaceMap b z) := by
  have hab' : a ^ 2 * b = a := by calc
    a ^ 2 * b = a * (a * b) := by ring
    _ = a := by rw [hab, mul_one]
  simp only [weakIntegrand, temporalTerm_scale a b hb, convectionTerm_scale a b hb,
    diffusionTerm_scale a b hb, pressureTerm_scale c b hb, hab', hbν, hcb,
    viscosityWeakIntegrand]
  ring

/-- The pressure factor is exactly h⁻¹ under the manuscript's normalization. -/
theorem viscosity_pressure_amplitude {h : ℝ} (hh : 0 < h) :
    h⁻¹ * Real.sqrt h = h ^ (-1 / 2 : ℝ) := by
  apply mul_right_cancel₀ (Real.sqrt_pos.mpr hh).ne'
  calc
    h⁻¹ * Real.sqrt h * Real.sqrt h = h⁻¹ * (Real.sqrt h)^2 := by ring
    _ = 1 := by rw [Real.sq_sqrt hh.le, inv_mul_cancel₀ hh.ne']
    _ = h ^ (-1 / 2 : ℝ) * Real.sqrt h :=
      (DerivativeScaling.viscosity_first_amplitude hh).symm

end UnforcedLeray.ViscosityTransport
