import UnforcedLeray.Analysis.Sturm.PotentialMultiplier
import UnforcedLeray.GaussianLogTrial

/-!
# Integrability of the actual Gaussian potential

A quantitative exponential bound proves that the completed ratio `g(x-2)` is
integrable on the positive half-line. The actual square-radius and exponential
Jacobians then prove `Wlog ∈ L¹(ℝ)`, and hence its actual positive square root
belongs to `L²`. No potential-integrability assumption is introduced.
-/

noncomputable section

namespace UnforcedLeray.Sturm

open MeasureTheory Set GaussianPotential GaussianTrial GaussianQuadratic GaussianLogTrial

/-- An explicit exponential upper bound on the positive tail of the ratio. -/
theorem bernoulliRatio_tail_bound (y : ℝ) (hy : 1 ≤ y) :
    bernoulliRatio y ≤ 2 * y * Real.exp (-y) := by
  have hy0 : 0 < y := by linarith
  have he : (2 : ℝ) ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hd : Real.exp y / 2 ≤ Real.exp y - 1 := by linarith
  rw [bernoulliRatio, ite_eq_right (ne_of_gt hy0)]
  calc
    y / (Real.exp y - 1) ≤ y / (Real.exp y / 2) :=
      div_le_div_of_nonneg_left hy0.le (by positivity) hd
    _ = 2 * y * Real.exp (-y) := by
      rw [Real.exp_neg]
      ring

/-- An integrable Gamma-type majorant valid on the entire positive half-line. -/
def ratioMajorant (x : ℝ) : ℝ :=
  (3 * Real.exp 3) * Real.exp (-x) + (2 * Real.exp 2) * (x * Real.exp (-x))

theorem shifted_ratio_le_majorant (x : ℝ) (hx : 0 < x) :
    bernoulliRatio (x - 2) ≤ ratioMajorant x := by
  by_cases hsmall : x ≤ 3
  · have hg := (bernoulli_bounds (x - 2)).2
    have habs : |x - 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hex : (1 : ℝ) ≤ Real.exp 3 * Real.exp (-x) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      linarith
    have htail : (0 : ℝ) ≤ (2 * Real.exp 2) * (x * Real.exp (-x)) := by positivity
    unfold ratioMajorant
    nlinarith
  · have hlarge : 1 ≤ x - 2 := by linarith
    have hg := bernoulliRatio_tail_bound (x - 2) hlarge
    have heq : Real.exp (-(x - 2)) = Real.exp 2 * Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hg
    have hprod : (0 : ℝ) ≤ Real.exp 2 * Real.exp (-x) := by positivity
    have hfirst : (0 : ℝ) ≤ (3 * Real.exp 3) * Real.exp (-x) := by positivity
    unfold ratioMajorant
    nlinarith

theorem integrable_ratioMajorant : IntegrableOn ratioMajorant (Ioi 0) := by
  have h0 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using integrable_pow_exp_neg 0
  have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi 0) := by
    simpa only [pow_one] using integrable_pow_exp_neg 1
  exact (h0.const_mul (3 * Real.exp 3)).add (h1.const_mul (2 * Real.exp 2))

/-- Integrability of the actual completed ratio without an additional weight. -/
theorem integrable_shifted_ratio :
    IntegrableOn (fun x : ℝ => bernoulliRatio (x - 2)) (Ioi 0) := by
  apply integrable_ratioMajorant.mono'
    (measurable_bernoulliRatio.comp (measurable_id.sub_const 2)).aestronglyMeasurable
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  change ‖bernoulliRatio (x - 2)‖ ≤ ratioMajorant x
  rw [Real.norm_eq_abs, abs_of_nonneg (bernoulli_bounds (x - 2)).1]
  exact shifted_ratio_le_majorant x hx

/-- Exact relation between the two checked Jacobians and the actual potential. -/
theorem Wlog_ratio_jacobian (t : ℝ) :
    Wlog t =
      (2 * bernoulliRatio (squareRadius (Real.exp t) - 2) * (Real.exp t / 2)) * Real.exp t := by
  rw [Wlog_eq_radial]
  unfold radialPotential
  ring

/-- The actual Gaussian log-radius potential belongs to `L¹(ℝ)`. -/
theorem integrable_Wlog : Integrable Wlog := by
  have hrad := integrable_squareRadius_substitution
    (fun x : ℝ => 2 * bernoulliRatio (x - 2)) (integrable_shifted_ratio.const_mul 2)
  have hlog := integrable_exp_substitution
    (fun r : ℝ => 2 * bernoulliRatio (squareRadius r - 2) * (r / 2)) hrad
  apply hlog.congr
  filter_upwards [] with t
  exact (Wlog_ratio_jacobian t).symm

/-- The exact potential integral after both changes of variables. -/
theorem integral_Wlog_eq_shifted_ratio :
    (∫ t : ℝ, Wlog t) = 2 * ∫ x : ℝ in Ioi 0, bernoulliRatio (x - 2) := by
  calc
    (∫ t : ℝ, Wlog t) = ∫ t : ℝ,
        (2 * bernoulliRatio (squareRadius (Real.exp t) - 2) * (Real.exp t / 2)) *
          Real.exp t := by
            apply integral_congr_ae
            filter_upwards [] with t
            exact Wlog_ratio_jacobian t
    _ = ∫ r : ℝ in Ioi 0, 2 * bernoulliRatio (squareRadius r - 2) * (r / 2) :=
      integral_exp_substitution
        (fun r : ℝ => 2 * bernoulliRatio (squareRadius r - 2) * (r / 2))
    _ = ∫ x : ℝ in Ioi 0, 2 * bernoulliRatio (x - 2) :=
      integral_squareRadius_substitution (fun x : ℝ => 2 * bernoulliRatio (x - 2))
    _ = 2 * ∫ x : ℝ in Ioi 0, bernoulliRatio (x - 2) := integral_const_mul _ _

/-- Square integrability of the existing, actual positive square-root potential. -/
theorem sqrtPotential_memLp_two : MemLp sqrtPotential 2 volume := by
  apply (memLp_two_iff_integrable_sq measurable_sqrtPotential.aestronglyMeasurable).2
  have he : (fun t : ℝ => sqrtPotential t ^ 2) = Wlog := by
    funext t
    exact Real.sq_sqrt (Wlog_pos t).le
  rw [he]
  exact integrable_Wlog

/-- The square-root potential's exact squared integral. -/
theorem integral_sqrtPotential_square :
    (∫ t : ℝ, sqrtPotential t ^ 2) = ∫ t : ℝ, Wlog t := by
  apply integral_congr_ae
  filter_upwards [] with t
  exact Real.sq_sqrt (Wlog_pos t).le

end UnforcedLeray.Sturm
