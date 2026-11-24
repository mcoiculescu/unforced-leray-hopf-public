import UnforcedLeray.Analysis.SpatialScaling
import UnforcedLeray.Analysis.WeakDerivative
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Tactic

/-!
# Distributional spatial derivatives under actual R³ dilation

The transformation `a • f (b • x)` has weak coordinate derivative
`(a*b) • g (b • x)` whenever g is the original weak derivative and b ≠ 0.
All compact-test pairings are proved integrable using the actual nonsingular
change of variables. No regularity or PDE property is presumed for the
transformed field. This supplies a step of viscosity normalization.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set MeasureTheory
open UnforcedLeray.SpatialScaling
open scoped ContDiff
namespace UnforcedLeray.DerivativeScaling

/-- Pull a spatial test back along the inverse coordinate dilation. -/
def inverseTest (b : ℝ) (φ : Space → ℝ) : Space → ℝ := fun y => φ (b⁻¹ • y)

theorem isSpatialTest_inverseTest {φ : Space → ℝ} (hφ : IsSpatialTest φ)
    {b : ℝ} (hb : b ≠ 0) : IsSpatialTest (inverseTest b φ) := by
  constructor
  · exact hφ.smooth.comp (contDiff_id.const_smul b⁻¹)
  · exact hφ.compact.comp_smul (inv_ne_zero hb)

theorem testDerivative_comp_smul (φ : Space → ℝ) (c : ℝ) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (fun y => φ (c • y)) x =
      c * spatialTestDerivative i φ (c • x) := by
  simp [spatialTestDerivative, fderiv_comp_smul, smul_eq_mul]

@[simp] theorem inverseTest_at_dilation (b : ℝ) (hb : b ≠ 0)
    (φ : Space → ℝ) (x : Space) : inverseTest b φ (b • x) = φ x := by
  simp [inverseTest, inv_smul_smul₀ hb]

theorem inverseTest_derivative_at_dilation (b : ℝ) (hb : b ≠ 0)
    (φ : Space → ℝ) (i : Fin 3) (x : Space) :
    spatialTestDerivative i (inverseTest b φ) (b • x) =
      b⁻¹ * spatialTestDerivative i φ x := by
  unfold inverseTest
  rw [testDerivative_comp_smul, inv_smul_smul₀ hb]

/-- The full left weak-derivative pairing transforms with coefficient a*b. -/
theorem left_pairing_transform (a b : ℝ) (hb : b ≠ 0) (i : Fin 3)
    (φ : Space → ℝ) (f : SpatialField) (x : Space) :
    spatialTestDerivative i φ x • spatialScale a b f x =
      (a * b) • (spatialTestDerivative i (inverseTest b φ) (b • x) • f (b • x)) := by
  rw [inverseTest_derivative_at_dilation b hb]
  simp only [spatialScale, smul_smul]
  congr 1
  field_simp

theorem right_pairing_transform (a b : ℝ) (hb : b ≠ 0)
    (φ : Space → ℝ) (g : SpatialField) (x : Space) :
    φ x • spatialScale (a * b) b g x =
      (a * b) • (inverseTest b φ (b • x) • g (b • x)) := by
  rw [inverseTest_at_dilation b hb]
  simp only [spatialScale, smul_smul]
  congr 1
  ring

/-- Genuine weak derivative transport under amplitude and coordinate scaling. -/
theorem hasWeakSpatialDerivative_spatialScale {i : Fin 3} {f g : SpatialField}
    (h : HasWeakSpatialDerivative i f g) (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasWeakSpatialDerivative i (spatialScale a b f) (spatialScale (a * b) b g) := by
  constructor
  · intro φ hφ
    have hi := ((h.left_integrable (inverseTest b φ)
      (isSpatialTest_inverseTest hφ hb)).comp_smul hb).fun_smul (a * b)
    simpa only [← left_pairing_transform a b hb i φ f] using hi
  · intro φ hφ
    have hi := ((h.right_integrable (inverseTest b φ)
      (isSpatialTest_inverseTest hφ hb)).comp_smul hb).fun_smul (a * b)
    simpa only [← right_pairing_transform a b hb φ g] using hi
  · intro φ hφ
    simp_rw [left_pairing_transform a b hb i φ f, right_pairing_transform a b hb φ g]
    rw [integral_smul, integral_smul,
      Measure.integral_comp_smul (volume : Measure Space)
        (fun y => spatialTestDerivative i (inverseTest b φ) y • f y) b,
      Measure.integral_comp_smul (volume : Measure Space)
        (fun y => inverseTest b φ y • g y) b,
      h.identity (inverseTest b φ) (isSpatialTest_inverseTest hφ hb)]
    simp only [smul_neg]

/-- The exact divergence pairing has the same scalar change-of-variables factor. -/
theorem solenoidal_pairing_transform (a b : ℝ) (hb : b ≠ 0)
    (φ : Space → ℝ) (f : SpatialField) (x : Space) :
    (∑ i : Fin 3, (spatialScale a b f x) i * spatialTestDerivative i φ x) =
      (a * b) * (∑ i : Fin 3, (f (b • x)) i *
        spatialTestDerivative i (inverseTest b φ) (b • x)) := by
  simp_rw [inverseTest_derivative_at_dilation b hb, spatialScale,
    PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- Distributional incompressibility is preserved by the actual spatial map. -/
theorem isSolenoidal_spatialScale {f : SpatialField} (h : IsSolenoidal f)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) : IsSolenoidal (spatialScale a b f) := by
  constructor
  · intro φ hφ
    have hi := ((h.integrable (inverseTest b φ)
      (isSpatialTest_inverseTest hφ hb)).comp_smul hb).const_mul (a * b)
    simpa only [← solenoidal_pairing_transform a b hb φ f] using hi
  · intro φ hφ
    simp_rw [solenoidal_pairing_transform a b hb φ f]
    rw [integral_const_mul,
      Measure.integral_comp_smul (volume : Measure Space)
        (fun y => ∑ i : Fin 3, (f y) i * spatialTestDerivative i (inverseTest b φ) y) b,
      h.identity (inverseTest b φ) (isSpatialTest_inverseTest hφ hb)]
    simp

/-- Two successive weak derivatives acquire the actual squared spatial factor. -/
theorem weak_second_spatialScale {i j : Fin 3} {f g q : SpatialField}
    (h₁ : HasWeakSpatialDerivative i f g) (h₂ : HasWeakSpatialDerivative j g q)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    HasWeakSpatialDerivative i (spatialScale a b f) (spatialScale (a * b) b g) ∧
    HasWeakSpatialDerivative j (spatialScale (a * b) b g) (spatialScale (a * b ^ 2) b q) := by
  constructor
  · exact hasWeakSpatialDerivative_spatialScale h₁ a hb
  · simpa only [pow_two, mul_assoc] using hasWeakSpatialDerivative_spatialScale h₂ (a * b) hb

/-- The first spatial derivative's amplitude in the actual viscosity transform. -/
theorem viscosity_first_amplitude {h : ℝ} (hh : 0 < h) :
    h ^ (-1 / 2 : ℝ) * Real.sqrt h = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hh]
  norm_num

/-- The second spatial derivative's amplitude in the actual viscosity transform. -/
theorem viscosity_second_amplitude {h : ℝ} (hh : 0 < h) :
    h ^ (-1 / 2 : ℝ) * (Real.sqrt h) ^ 2 = Real.sqrt h := by
  rw [pow_two, ← mul_assoc, viscosity_first_amplitude hh, one_mul]

/-- Weak first derivative of h^(-1/2) f(sqrt h x), with the exact unit amplitude. -/
theorem weak_derivative_viscosityScale {i : Fin 3} {f g : SpatialField}
    (hfg : HasWeakSpatialDerivative i f g) {h : ℝ} (hh : 0 < h) :
    HasWeakSpatialDerivative i (viscosityScale h f) (spatialScale 1 (Real.sqrt h) g) := by
  simpa only [viscosityScale, viscosity_first_amplitude hh] using
    hasWeakSpatialDerivative_spatialScale hfg (h ^ (-1 / 2 : ℝ)) (Real.sqrt_pos.mpr hh).ne'

/-- Exact first and second weak derivative transport for viscosity normalization. -/
theorem weak_second_viscosityScale {i j : Fin 3} {f g q : SpatialField}
    (hfg : HasWeakSpatialDerivative i f g) (hgq : HasWeakSpatialDerivative j g q)
    {h : ℝ} (hh : 0 < h) :
    HasWeakSpatialDerivative i (viscosityScale h f) (spatialScale 1 (Real.sqrt h) g) ∧
    HasWeakSpatialDerivative j (spatialScale 1 (Real.sqrt h) g)
      (spatialScale (Real.sqrt h) (Real.sqrt h) q) := by
  simpa only [viscosityScale, viscosity_first_amplitude hh, viscosity_second_amplitude hh] using
    weak_second_spatialScale hfg hgq (h ^ (-1 / 2 : ℝ)) (Real.sqrt_pos.mpr hh).ne'

theorem isSolenoidal_viscosityScale {f : SpatialField} (hf : IsSolenoidal f)
    {h : ℝ} (hh : 0 < h) : IsSolenoidal (viscosityScale h f) :=
  isSolenoidal_spatialScale hf _ (Real.sqrt_pos.mpr hh).ne'

end UnforcedLeray.DerivativeScaling
