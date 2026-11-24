import UnforcedLeray.Analysis.Rayleigh.GaussianMode
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Normalizing a genuine nonzero Gaussian annular mode

A nonzero point of a continuous mode on a nondegenerate interval forces its
actual squared Lebesgue mass to be positive. The full Gaussian Rayleigh ODE
is homogeneous under constant scaling. Scaling by the reciprocal square root
of that mass then produces an actual mode of mass exactly one. Positivity and
finiteness of the mass are proved, rather than supplied as a certificate.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh
open Sturm

/-- The actual squared L² mass on a logarithmic annulus. -/
def annularMass (F : ℝ → ℂ) (l r : ℝ) : ℝ := ∫ t in Ioc l r, ‖F t‖ ^ 2

/-- Ordinary squared-mass scaling for a constant complex amplitude. -/
theorem annularMass_const_smul (a : ℂ) (F : ℝ → ℂ) (l r : ℝ) :
    annularMass (a • F) l r = ‖a‖ ^ 2 * annularMass F l r := by
  unfold annularMass
  simp_rw [Pi.smul_apply, norm_smul, mul_pow]
  exact integral_const_mul _ _

/-- The normalization amplitude, used only with proved positive mass. -/
def annularNormalizationFactor (F : ℝ → ℂ) (l r : ℝ) : ℝ :=
  (Real.sqrt (annularMass F l r))⁻¹

/-- The actual normalized profile; the real positive amplitude is viewed in ℂ. -/
def normalizedGaussianProfile (F : ℝ → ℂ) (l r : ℝ) : ℝ → ℂ :=
  (annularNormalizationFactor F l r : ℂ) • F

namespace GaussianAnnularMode
variable {c : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : GaussianAnnularMode c F l r)
include h

/-- Finiteness of the actual squared mass follows from the mode's C² regularity. -/
theorem mass_integrable : IntegrableOn (fun t => ‖F t‖ ^ 2) (Ioc l r) :=
  (h.regularity.continuous.norm.pow 2).integrableOn_Ioc

/-- A nonzero continuous mode cannot have zero L² mass on a genuine interval. -/
theorem mass_pos (hlr : l < r) (hnonzero : ∃ t ∈ Icc l r, F t ≠ 0) :
    0 < annularMass F l r := by
  have hn : ∃ t ∈ Icc l r, 0 < ‖F t‖ ^ 2 := by
    obtain ⟨t, ht, hne⟩ := hnonzero
    exact ⟨t, ht, sq_pos_of_pos (norm_pos_iff.mpr hne)⟩
  have hi := intervalIntegral.integral_pos hlr
    (h.regularity.continuous.norm.pow 2).continuousOn
    (fun t _ => sq_nonneg ‖F t‖) hn
  simpa only [intervalIntegral.integral_of_le hlr.le, annularMass, Pi.pow_apply] using hi

/-- Constant scaling preserves the actual Gaussian differential equation,
regularity, spectral speed and both Dirichlet boundary values. -/
theorem const_smul (a : ℂ) : GaussianAnnularMode c (a • F) l r := by
  refine ⟨h.ordered, h.upper_half_plane, h.regularity.const_smul a,
    ?_, ?_, ?_⟩
  · simp only [Pi.smul_apply, h.left_endpoint, smul_zero]
  · simp only [Pi.smul_apply, h.right_endpoint, smul_zero]
  · intro t ht
    have hd : deriv (a • F) = a • deriv F := by
      funext x
      exact deriv_const_smul_field a F
    have hdd : deriv (deriv (a • F)) = a • deriv (deriv F) := by
      rw [hd]
      funext x
      exact deriv_const_smul_field a (deriv F)
    rw [hdd]
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      _ = a * (((neutralOmega t : ℂ) - c) * (deriv (deriv F) t - 4 * F t) -
          (gaussianRayleighCoefficient t : ℂ) * F t) := by ring
      _ = 0 := by rw [h.equation t ht, mul_zero]

/-- The explicitly normalized function still solves the actual Rayleigh ODE. -/
theorem normalized_is_mode : GaussianAnnularMode c (normalizedGaussianProfile F l r) l r :=
  h.const_smul (annularNormalizationFactor F l r : ℂ)

/-- The normalization gives mass exactly one; positivity is derived from the
nonzero point and the actual interval, rather than assumed separately. -/
theorem normalized_mass_one (hlr : l < r) (hnonzero : ∃ t ∈ Icc l r, F t ≠ 0) :
    (∫ t in Ioc l r, ‖normalizedGaussianProfile F l r t‖ ^ 2) = 1 := by
  have hp := h.mass_pos hlr hnonzero
  change annularMass (normalizedGaussianProfile F l r) l r = 1
  rw [normalizedGaussianProfile, annularMass_const_smul]
  simp only [annularNormalizationFactor, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, inv_pow, Real.sq_sqrt hp.le]
  exact inv_mul_cancel₀ hp.ne'

end GaussianAnnularMode

/-- Every actual nonzero Gaussian annular mode on a nondegenerate interval has
an actual unit-mass representative with the identical unstable speed. -/
theorem exists_normalized_gaussian_mode {c : ℂ} {F : ℝ → ℂ} {l r : ℝ}
    (h : GaussianAnnularMode c F l r) (hlr : l < r)
    (hnonzero : ∃ t ∈ Icc l r, F t ≠ 0) :
    ∃ G : ℝ → ℂ, GaussianAnnularMode c G l r ∧
      (∫ t in Ioc l r, ‖G t‖ ^ 2) = 1 :=
  ⟨normalizedGaussianProfile F l r, h.normalized_is_mode,
    h.normalized_mass_one hlr hnonzero⟩

end UnforcedLeray.Rayleigh
