import UnforcedLeray.Analysis.GaussianVortex.RadialProfile
import UnforcedLeray.Analysis.Sturm.NeutralPotentialRegularity
import UnforcedLeray.GaussianQuadratic

/-!
# The smooth completed coefficient in Lin's rotating-flow equation

The actual quotient has a removable value at r²=8. The definitions here use
the previously checked smooth completion of y/(exp(y)−1). They agree with the
manuscript's derivative quotient away from the critical radius and identify
its logarithmic-coordinate potential with the existing Wlog exactly.
-/

noncomputable section
open scoped ContDiff
namespace UnforcedLeray.GaussianVortex
open GaussianTrial

/-- The completed positive neutral radial potential v. -/
def radialNeutralPotential (r : ℝ) : ℝ := bernoulliRatio (r ^ 2 / 4 - 2)

/-- Lin's completed rotating-flow potential K=r v. -/
def radialLinPotential (r : ℝ) : ℝ := r * radialNeutralPotential r

theorem radialNeutralPotential_smooth : ContDiff ℝ ∞ radialNeutralPotential := by
  apply Sturm.bernoulliRatio_smooth.comp
  fun_prop

theorem radialLinPotential_smooth : ContDiff ℝ ∞ radialLinPotential :=
  contDiff_id.mul radialNeutralPotential_smooth

theorem radialNeutralPotential_pos (r : ℝ) : 0 < radialNeutralPotential r :=
  bernoulliRatio_pos _

theorem radialLinPotential_pos {r : ℝ} (hr : 0 < r) : 0 < radialLinPotential r :=
  mul_pos hr (radialNeutralPotential_pos r)

theorem radialNeutralPotential_at_critical {r : ℝ} (hr : r ^ 2 = 8) :
    radialNeutralPotential r = 1 := by
  norm_num [radialNeutralPotential, hr, bernoulliRatio]

theorem radialLinPotential_at_critical {r : ℝ} (hr : r ^ 2 = 8) :
    radialLinPotential r = r := by
  simp only [radialLinPotential, radialNeutralPotential_at_critical hr, mul_one]

theorem radialNeutralPotential_eq_quotient {r : ℝ} (hr : r ^ 2 ≠ 8) :
    radialNeutralPotential r = -radialK r / (radialOmega r - Real.exp (-2)) :=
  (radial_potential_quotient hr).symm

theorem radialLinPotential_eq_derivative_quotient {r : ℝ} (hr : r ^ 2 ≠ 8) :
    radialLinPotential r =
      -(r * deriv (deriv radialOmega) r + 3 * deriv radialOmega r) /
        (radialOmega r - Real.exp (-2)) :=
  (radial_lin_coefficient hr).symm

/-- The cancellation remains valid at the removable point. -/
theorem radialLinPotential_mul_difference (r : ℝ) :
    radialLinPotential r * (radialOmega r - Real.exp (-2)) = -r * radialK r := by
  have h := bernoulliRatio_mul_exp_difference (r ^ 2 / 4 - 2)
  change r * bernoulliRatio (r ^ 2 / 4 - 2) *
    (radialOmega r - Real.exp (-2)) = -r * radialK r
  have he : bernoulliRatio (r ^ 2 / 4 - 2) *
      (radialOmega r - Real.exp (-2)) = -radialK r := by
    simpa only [sub_add_cancel, radialOmega, radialK, neg_mul] using h
  linear_combination r * he

/-- The trial-function potential is this same completed neutral coefficient. -/
theorem radialNeutralPotential_eq_trialPotential (r : ℝ) :
    radialNeutralPotential r = GaussianQuadratic.radialPotential r := rfl

/-- The log-radius Jacobian converts Lin's coefficient into the actual Wlog. -/
theorem radialLinPotential_exp_eq_Wlog (t : ℝ) :
    Real.exp t * radialLinPotential (Real.exp t) = GaussianPotential.Wlog t := by
  rw [GaussianPotential.Wlog, Sturm.W_eq_completed_ratio]
  unfold radialLinPotential radialNeutralPotential
  rw [← exp_sq_eq_exp_twice]
  ring

/-- The actual coefficient is bounded on every closed radial annulus. -/
theorem radialLinPotential_bounded_on_annulus (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, |radialLinPotential r| ≤ C := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc a b)).image
    (continuous_norm.comp radialLinPotential_smooth.continuous)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun r hr => ?_⟩
  have h := hC (Set.mem_image_of_mem (fun r : ℝ => ‖radialLinPotential r‖) hr)
  have h' : |radialLinPotential r| ≤ C := by simpa only [Real.norm_eq_abs] using h
  exact h'.trans (le_max_left _ _)

/-- The two endpoint angular speeds differ on every genuine positive annulus. -/
theorem radialOmega_annulus_endpoints_ne {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    radialOmega a ≠ radialOmega b := by
  exact (strictAntiOn_radialOmega ha (ha.trans hab.le) hab).ne'

end UnforcedLeray.GaussianVortex
