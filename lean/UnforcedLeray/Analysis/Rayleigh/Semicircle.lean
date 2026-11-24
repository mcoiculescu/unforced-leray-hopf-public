import UnforcedLeray.Analysis.Rayleigh.SemicircleTransform
import UnforcedLeray.Analysis.Rayleigh.SemicircleEnergy
import UnforcedLeray.Analysis.Rayleigh.SemicircleWeight
import UnforcedLeray.Analysis.Rayleigh.SemicircleMoments
import UnforcedLeray.Analysis.Rayleigh.SpeedBound

/-!
# The rotating semicircle for actual Gaussian annular Rayleigh modes

The original Gaussian equation yields a nonsingular quotient equation. Genuine
Dirichlet integration by parts produces a complex moment identity, and actual
normalization makes its weight nonzero. The resulting semicircle is therefore
a consequence of the differential equation, with no spectral estimate premise.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh
open Sturm
namespace GaussianAnnularMode
variable {c : ℂ} {F : ℝ → ℂ} {l r : ℝ} (h : GaussianAnnularMode c F l r)
include h

/-- The weighted moment identity is derived from the actual Gaussian ODE. -/
theorem semicircle_moment_zero :
    (∫ t in Ioc l r, (semicircleWeight (semicircleQuotient c F) t : ℂ) *
      ((neutralOmega t : ℂ) - c) ^ 2) = 0 := by
  have hH : ContDiff ℝ 2 (semicircleProfile c) :=
    (semicircleProfile_smooth c).of_le (by simp)
  have hG := semicircleQuotient_contDiff h.regularity h.upper_half_plane
  have he := weighted_dirichlet_energy_zero hH hG h.ordered
    h.semicircleQuotient_left_endpoint h.semicircleQuotient_right_endpoint
    h.semicircle_transformed_equation
  calc
    _ = ∫ t in Ioc l r, semicircleProfile c t ^ 2 *
        (semicircleEnergyDensity (semicircleQuotient c F) t : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t _
      dsimp only
      rw [semicircleProfile_sq_eq_exp]
      simp only [semicircleWeight, Complex.ofReal_mul]
      ring
    _ = 0 := he

/-- Every nontrivial genuine Gaussian annular mode satisfies the rotating
semicircle. Nontriviality is expressed by its actual nonzero finite-interval mass. -/
theorem semicircle_of_mass_ne_zero
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) ≠ 0) :
    (c.re - 1 / 2) ^ 2 + c.im ^ 2 ≤ 1 / 4 ∧ 0 < c.re ∧ c.re < 1 := by
  have hG := semicircleQuotient_contDiff h.regularity h.upper_half_plane
  have hw := semicircleWeight_continuous hG
  have hp : 0 < ∫ t in Ioc l r, semicircleWeight (semicircleQuotient c F) t :=
    semicircleWeight_integral_pos_of_mass_ne_zero hG
      (fun t => (semicircleProfile_mul_quotient h.upper_half_plane F t).symm) hmass
  exact semicircle_of_weighted_moment_zero hw continuous_neutralOmega
    (semicircleWeight_nonneg _) (fun t => (neutralOmega_pos t).le)
    (fun t => (neutralOmega_lt_one t).le) h.upper_half_plane l r hp
    h.semicircle_moment_zero

/-- Every normalized genuine unstable Gaussian annular mode has its complex
speed inside the closed disk with diameter `[0,1]`; its real part is strictly
between the endpoint angular speeds. -/
theorem normalized_semicircle
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    (c.re - 1 / 2) ^ 2 + c.im ^ 2 ≤ 1 / 4 ∧ 0 < c.re ∧ c.re < 1 := by
  apply h.semicircle_of_mass_ne_zero
  rw [hmass]
  norm_num

/-- The imaginary growth parameter has the precise upper bound one half. -/
theorem normalized_im_le_half
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) : c.im ≤ 1 / 2 := by
  have hcircle := (h.normalized_semicircle hmass).1
  have hc := h.upper_half_plane
  nlinarith [sq_nonneg (c.re - 1 / 2)]

/-- The rotating semicircle also improves the compactness disk to the unit disk. -/
theorem normalized_speed_norm_lt_one
    (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) : ‖c‖ < 1 := by
  obtain ⟨hcircle, _, hre⟩ := h.normalized_semicircle hmass
  have hnorm : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg c]

end GaussianAnnularMode
end UnforcedLeray.Rayleigh
