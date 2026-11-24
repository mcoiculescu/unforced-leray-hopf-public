import UnforcedLeray.Analysis.GaussianVortex.PlanarDefs
import UnforcedLeray.Analysis.GaussianVortex.GaussianMoments
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual integrals of the planar Gaussian vortex

All full-plane integrals use Lebesgue measure on the real Cartesian plane.
Gaussian product factorizations and Fubini give the circulation cancellation
and the Euclidean kinetic-energy integral. The L² conclusion also verifies
the norm used by the real product Banach space.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.GaussianVortex

/-- The isotropic Gaussian with positive inverse-variance parameter. -/
def gaussian2D (b : ℝ) (z : Plane) : ℝ := Real.exp (-b * radiusSq z)

theorem gaussian2D_factor (b : ℝ) (z : Plane) :
    gaussian2D b z = Real.exp (-b * z.1 ^ 2) * Real.exp (-b * z.2 ^ 2) := by
  unfold gaussian2D radiusSq
  rw [← Real.exp_add]
  congr 1
  ring

theorem planarGaussian_eq_gaussian2D : planarGaussian = gaussian2D (1 / 4) := by
  funext z
  unfold planarGaussian gaussian2D
  congr 1
  ring

theorem integrable_gaussian2D {b : ℝ} (hb : 0 < b) : Integrable (gaussian2D b) := by
  have h := (integrable_exp_neg_mul_sq hb).mul_prod (integrable_exp_neg_mul_sq hb)
  exact h.congr (Filter.Eventually.of_forall fun z => (gaussian2D_factor b z).symm)

theorem integral_gaussian2D {b : ℝ} (hb : 0 < b) :
    (∫ z : Plane, gaussian2D b z) = Real.pi / b := by
  simp_rw [gaussian2D_factor]
  change (∫ z : ℝ × ℝ, Real.exp (-b * z.1 ^ 2) * Real.exp (-b * z.2 ^ 2)
    ∂(volume.prod volume)) = _
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-b * x ^ 2))
    (fun y : ℝ => Real.exp (-b * y ^ 2))]
  simp only [integral_gaussian]
  simpa only [pow_two] using Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)

theorem integrable_planarGaussian : Integrable planarGaussian := by
  rw [planarGaussian_eq_gaussian2D]
  exact integrable_gaussian2D (by norm_num)

theorem integral_planarGaussian : (∫ z : Plane, planarGaussian z) = 4 * Real.pi := by
  rw [planarGaussian_eq_gaussian2D, integral_gaussian2D (by norm_num)]
  ring

theorem integrable_streamfunction : Integrable streamfunction :=
  integrable_planarGaussian.const_mul (-2)

theorem integral_streamfunction : (∫ z : Plane, streamfunction z) = -8 * Real.pi := by
  simp only [streamfunction]
  rw [integral_const_mul, integral_planarGaussian]
  ring

theorem integrable_pressure : Integrable pressure := by
  have h : pressure = fun z => -gaussian2D (1 / 2) z := by
    funext z
    unfold pressure gaussian2D
    congr 2
    ring
  rw [h]
  exact (integrable_gaussian2D (by norm_num)).neg

theorem integral_pressure : (∫ z : Plane, pressure z) = -2 * Real.pi := by
  have h : pressure = fun z => -gaussian2D (1 / 2) z := by
    funext z
    unfold pressure gaussian2D
    congr 2
    ring
  rw [h, integral_neg, integral_gaussian2D (by norm_num)]
  ring

/-- Both Cartesian velocity components are absolutely integrable. -/
theorem integrable_velocity : Integrable velocity := by
  have hg := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 / 4 by norm_num)
  have hx := integrable_mul_exp_neg_mul_sq (show (0 : ℝ) < 1 / 4 by norm_num)
  have h1 : Integrable (fun z : Plane => (velocity z).1) := by
    have h := hg.mul_prod hx.neg
    exact h.congr (Filter.Eventually.of_forall fun z => by
      dsimp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
      unfold velocity
      dsimp only
      rw [planarGaussian_eq_gaussian2D, gaussian2D_factor]
      ring)
  have h2 : Integrable (fun z : Plane => (velocity z).2) := by
    have h := hx.mul_prod hg
    exact h.congr (Filter.Eventually.of_forall fun z => by
      dsimp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
      unfold velocity
      dsimp only
      rw [planarGaussian_eq_gaussian2D, gaussian2D_factor]
      ring)
  exact h1.prodMk h2

/-- The actual Euclidean sum of the squares of the Cartesian components. -/
def velocityEnergyDensity (z : Plane) : ℝ := (velocity z).1 ^ 2 + (velocity z).2 ^ 2

theorem velocityEnergyDensity_eq (z : Plane) :
    velocityEnergyDensity z = radiusSq z * gaussian2D (1 / 2) z := by
  have he : (planarGaussian z) ^ 2 = gaussian2D (1 / 2) z := by
    rw [pow_two, planarGaussian, ← Real.exp_add]
    unfold gaussian2D
    congr 1
    ring
  unfold velocityEnergyDensity velocity
  dsimp only
  rw [mul_pow, mul_pow, neg_sq, he]
  unfold radiusSq
  ring

theorem norm_velocity_sq_le (z : Plane) : ‖velocity z‖ ^ 2 ≤ velocityEnergyDensity z := by
  unfold velocityEnergyDensity
  rw [Prod.norm_def]
  rcases le_total ‖(velocity z).1‖ ‖(velocity z).2‖ with h | h
  · rw [max_eq_right h, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (velocity z).1]
  · rw [max_eq_left h, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (velocity z).2]


/-- Integrability of the actual first coordinate second moment in the plane. -/
theorem integrable_firstSq_mul_gaussian2D {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Plane => z.1 ^ 2 * gaussian2D b z) := by
  have h := (integrable_gaussian_sq_moment hb).mul_prod (integrable_exp_neg_mul_sq hb)
  exact h.congr (Filter.Eventually.of_forall fun z => by
    dsimp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
    rw [gaussian2D_factor]
    ring)

/-- Integrability of the actual second coordinate second moment in the plane. -/
theorem integrable_secondSq_mul_gaussian2D {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Plane => z.2 ^ 2 * gaussian2D b z) := by
  have h := (integrable_exp_neg_mul_sq hb).mul_prod (integrable_gaussian_sq_moment hb)
  exact h.congr (Filter.Eventually.of_forall fun z => by
    dsimp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
    rw [gaussian2D_factor]
    ring)

theorem integral_firstSq_mul_gaussian2D {b : ℝ} (hb : 0 < b) :
    (∫ z : Plane, z.1 ^ 2 * gaussian2D b z) = Real.pi / (2 * b ^ 2) := by
  have he : (fun z : Plane => z.1 ^ 2 * gaussian2D b z) =
      fun z => (z.1 ^ 2 * Real.exp (-b * z.1 ^ 2)) * Real.exp (-b * z.2 ^ 2) := by
    funext z
    rw [gaussian2D_factor]
    ring
  rw [he]
  change (∫ z : ℝ × ℝ, (z.1 ^ 2 * Real.exp (-b * z.1 ^ 2)) *
    Real.exp (-b * z.2 ^ 2) ∂(volume.prod volume)) = _
  rw [integral_prod_mul (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2))
    (fun y : ℝ => Real.exp (-b * y ^ 2)), integral_gaussian_sq_moment hb, integral_gaussian]
  calc
    _ = (2 * b)⁻¹ * (Real.sqrt (Real.pi / b)) ^ 2 := by ring
    _ = (2 * b)⁻¹ * (Real.pi / b) := by
      rw [Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)]
    _ = _ := by field_simp [hb.ne']

theorem integral_secondSq_mul_gaussian2D {b : ℝ} (hb : 0 < b) :
    (∫ z : Plane, z.2 ^ 2 * gaussian2D b z) = Real.pi / (2 * b ^ 2) := by
  have he : (fun z : Plane => z.2 ^ 2 * gaussian2D b z) =
      fun z => Real.exp (-b * z.1 ^ 2) * (z.2 ^ 2 * Real.exp (-b * z.2 ^ 2)) := by
    funext z
    rw [gaussian2D_factor]
    ring
  rw [he]
  change (∫ z : ℝ × ℝ, Real.exp (-b * z.1 ^ 2) *
    (z.2 ^ 2 * Real.exp (-b * z.2 ^ 2)) ∂(volume.prod volume)) = _
  rw [integral_prod_mul (fun x : ℝ => Real.exp (-b * x ^ 2))
    (fun y : ℝ => y ^ 2 * Real.exp (-b * y ^ 2)), integral_gaussian, integral_gaussian_sq_moment hb]
  calc
    _ = (2 * b)⁻¹ * (Real.sqrt (Real.pi / b)) ^ 2 := by ring
    _ = (2 * b)⁻¹ * (Real.pi / b) := by
      rw [Real.sq_sqrt (div_nonneg Real.pi_pos.le hb.le)]
    _ = _ := by field_simp [hb.ne']

theorem integrable_radiusSq_mul_gaussian2D {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Plane => radiusSq z * gaussian2D b z) := by
  have h := (integrable_firstSq_mul_gaussian2D hb).add (integrable_secondSq_mul_gaussian2D hb)
  exact h.congr (Filter.Eventually.of_forall fun z => by
    dsimp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
    unfold radiusSq
    ring)

theorem integral_radiusSq_mul_gaussian2D {b : ℝ} (hb : 0 < b) :
    (∫ z : Plane, radiusSq z * gaussian2D b z) = Real.pi / b ^ 2 := by
  simp_rw [radiusSq, add_mul]
  rw [integral_add (integrable_firstSq_mul_gaussian2D hb)
    (integrable_secondSq_mul_gaussian2D hb),
    integral_firstSq_mul_gaussian2D hb, integral_secondSq_mul_gaussian2D hb]
  ring

theorem integrable_radiusSq_mul_planarGaussian :
    Integrable (fun z : Plane => radiusSq z * planarGaussian z) := by
  rw [planarGaussian_eq_gaussian2D]
  exact integrable_radiusSq_mul_gaussian2D (by norm_num)

theorem integral_radiusSq_mul_planarGaussian :
    (∫ z : Plane, radiusSq z * planarGaussian z) = 16 * Real.pi := by
  rw [planarGaussian_eq_gaussian2D, integral_radiusSq_mul_gaussian2D (by norm_num)]
  ring

/-- Actual Gaussian vorticity is absolutely integrable on the whole plane. -/
theorem integrable_vorticity : Integrable vorticity := by
  have h := (integrable_planarGaussian.const_mul 2).sub
    (integrable_radiusSq_mul_planarGaussian.const_mul (1 / 2))
  exact h.congr (Filter.Eventually.of_forall fun z => by
    dsimp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
    unfold vorticity
    ring)

/-- Zero circulation, obtained by evaluating both actual Gaussian moments. -/
theorem integral_vorticity_eq_zero : (∫ z : Plane, vorticity z) = 0 := by
  have he : vorticity = fun z =>
      2 * planarGaussian z - (1 / 2) * (radiusSq z * planarGaussian z) := by
    funext z
    unfold vorticity
    ring
  rw [he, integral_sub (integrable_planarGaussian.const_mul 2)
    (integrable_radiusSq_mul_planarGaussian.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul, integral_planarGaussian,
    integral_radiusSq_mul_planarGaussian]
  ring

/-- The Euclidean component-squared kinetic-energy density is integrable. -/
theorem integrable_velocityEnergyDensity : Integrable velocityEnergyDensity := by
  have h := integrable_radiusSq_mul_gaussian2D (show (0 : ℝ) < 1 / 2 by norm_num)
  exact h.congr (Filter.Eventually.of_forall fun z => (velocityEnergyDensity_eq z).symm)

/-- The unhalved Euclidean kinetic-energy integral of the unit vortex is 4π. -/
theorem integral_velocityEnergyDensity :
    (∫ z : Plane, velocityEnergyDensity z) = 4 * Real.pi := by
  simp_rw [velocityEnergyDensity_eq]
  rw [integral_radiusSq_mul_gaussian2D (by norm_num)]
  ring

/-- The concrete velocity is in L² for the ordinary product norm. -/
theorem velocity_memLp_two : MemLp velocity 2 volume := by
  have hm : AEStronglyMeasurable velocity volume :=
    contDiff_velocity.continuous.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact integrable_velocityEnergyDensity.mono'
    (contDiff_velocity.continuous.norm.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact norm_velocity_sq_le z)

end UnforcedLeray.GaussianVortex
