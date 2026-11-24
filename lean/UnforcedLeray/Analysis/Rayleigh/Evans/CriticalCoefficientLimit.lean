import UnforcedLeray.Analysis.Rayleigh.Evans.Coefficients
import UnforcedLeray.Analysis.Sturm.PotentialIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual vertical critical-speed coefficient limit

The completed neutral coefficient is defined separately from the totalized
Rayleigh quotient. Along the vertical upper-half-plane approach, the exact
Gaussian cancellation bounds the difference by the integrable potential Wlog.
Its limit is zero away from the single critical log-radius, hence in L¹.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace UnforcedLeray.Rayleigh.Evans
open Sturm GaussianPotential

/-- The smooth completed neutral equation coefficient. -/
def neutralPotential (α t : ℝ) : ℂ := (α : ℂ) ^ 2 - (Wlog t : ℂ)

/-- Vertical approach to the actual critical speed from the upper half-plane. -/
def verticalCriticalSpeed (ε : ℝ) : ℂ :=
  (gaussianCriticalSpeed : ℂ) + (ε : ℂ) * Complex.I

@[simp] theorem verticalCriticalSpeed_im (ε : ℝ) :
    (verticalCriticalSpeed ε).im = ε := by simp [verticalCriticalSpeed]

@[simp] theorem verticalCriticalSpeed_zero :
    verticalCriticalSpeed 0 = (gaussianCriticalSpeed : ℂ) := by
  simp [verticalCriticalSpeed]

theorem contDiff_neutralPotential (α : ℝ) : ContDiff ℝ ∞ (neutralPotential α) :=
  contDiff_const.sub (Complex.ofRealCLM.contDiff.comp Wlog_smooth)

theorem continuous_neutralPotential (α : ℝ) : Continuous (neutralPotential α) :=
  (contDiff_neutralPotential α).continuous

theorem gaussianOffset_ne_zero_off_critical {t : ℝ} (ht : t ≠ neutralCriticalTime) :
    gaussianOffset t ≠ 0 := by
  intro hz
  apply neutralProfile_ne_zero ht
  change Real.exp t * gaussianOffset t = 0
  rw [hz, mul_zero]

/-- The actual difference is the critical-layer remainder, including at the
critical radius whenever ε is positive. -/
theorem rayleighPotential_sub_neutral_vertical (α t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    rayleighPotential α t (verticalCriticalSpeed ε) - neutralPotential α t =
      -(Wlog t : ℂ) * ((ε : ℂ) * Complex.I) /
        ((gaussianOffset t : ℂ) - (ε : ℂ) * Complex.I) := by
  have hd : (gaussianOffset t : ℂ) - (ε : ℂ) * Complex.I ≠ 0 := by
    apply criticalDenominator_ne_zero
    simpa using hε
  unfold rayleighPotential neutralPotential
  rw [gaussian_denominator_eq]
  simp only [shiftedSpeed, verticalCriticalSpeed, add_sub_cancel_left,
    gaussianRayleighCoefficient, Complex.ofReal_neg, Complex.ofReal_mul]
  field_simp
  ring

/-- The exact Gaussian cancellation gives an integrable, ε-independent bound. -/
theorem norm_rayleighPotential_sub_neutral_vertical_le (α t : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ‖rayleighPotential α t (verticalCriticalSpeed ε) - neutralPotential α t‖ ≤ Wlog t := by
  rw [rayleighPotential_sub_neutral_vertical α t hε, norm_div, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Wlog_pos t)]
  have hd : 0 < ‖(gaussianOffset t : ℂ) - (ε : ℂ) * Complex.I‖ := by
    apply norm_pos_iff.mpr
    apply criticalDenominator_ne_zero
    simpa using hε
  apply (div_le_iff₀ hd).mpr
  apply mul_le_mul_of_nonneg_left _ (Wlog_pos t).le
  have hi := Complex.abs_im_le_norm
    ((gaussianOffset t : ℂ) - (ε : ℂ) * Complex.I)
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs] using hi

/-- Pointwise convergence holds off the unique critical point. No false
identification of the totalized quotient at that point is used. -/
theorem tendsto_rayleighPotential_vertical_of_ne_critical (α : ℝ) {t : ℝ}
    (ht : t ≠ neutralCriticalTime) :
    Tendsto (fun ε : ℝ => rayleighPotential α t (verticalCriticalSpeed ε))
      (𝓝[>] 0) (𝓝 (neutralPotential α t)) := by
  have hd : (neutralOmega t : ℂ) - (gaussianCriticalSpeed : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast gaussianOffset_ne_zero_off_critical ht
  have hc : ContinuousAt (fun ε : ℝ =>
      rayleighPotential α t (verticalCriticalSpeed ε)) 0 := by
    unfold rayleighPotential
    apply ContinuousAt.add continuousAt_const
    apply ContinuousAt.div continuousAt_const
    · unfold verticalCriticalSpeed
      fun_prop
    · simpa using hd
  have he : rayleighPotential α t (verticalCriticalSpeed 0) = neutralPotential α t := by
    simp only [verticalCriticalSpeed_zero, rayleighPotential, neutralPotential,
      gaussianRayleighCoefficient, gaussianOffset, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_sub]
    field_simp
    ring
  simpa only [he] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The actual coefficient difference is integrable on the entire log-radius
line; neither coefficient itself is asserted integrable. -/
theorem integrable_rayleighPotential_sub_neutral_vertical (α : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun t => rayleighPotential α t (verticalCriticalSpeed ε) -
      neutralPotential α t) := by
  have hc : Continuous (fun t => rayleighPotential α t (verticalCriticalSpeed ε) -
      neutralPotential α t) :=
    (continuous_rayleighPotential α (by simpa [upperHalfPlane] using hε)).sub
      (continuous_neutralPotential α)
  apply integrable_Wlog.mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun t => norm_rayleighPotential_sub_neutral_vertical_le α t hε)

/-- Genuine L¹ convergence on the whole line along the vertical approach. -/
theorem tendsto_integral_norm_criticalPotential_sub_neutral (α : ℝ) :
    Tendsto (fun ε : ℝ => ∫ t,
      ‖rayleighPotential α t (verticalCriticalSpeed ε) - neutralPotential α t‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun t => ‖rayleighPotential α t (verticalCriticalSpeed ε) -
        neutralPotential α t‖) volume := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integrable_rayleighPotential_sub_neutral_vertical α hε).norm.aestronglyMeasurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ t : ℝ,
      ‖‖rayleighPotential α t (verticalCriticalSpeed ε) - neutralPotential α t‖‖ ≤
        Wlog t := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ae_of_all _ (fun t => by
      simpa only [norm_norm] using norm_rayleighPotential_sub_neutral_vertical_le α t hε)
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ =>
      ‖rayleighPotential α t (verticalCriticalSpeed ε) - neutralPotential α t‖)
      (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [(volume : Measure ℝ).ae_ne neutralCriticalTime] with t ht
    have h := ((tendsto_rayleighPotential_vertical_of_ne_critical α ht).sub_const
      (neutralPotential α t)).norm
    simpa only [sub_self, norm_zero] using h
  simpa using tendsto_integral_filter_of_dominated_convergence Wlog hmeas hbound
    integrable_Wlog hlim

/-- In particular the actual difference converges in L¹ on every set, hence
on any finite annulus. No endpoint placement relative to the critical point
is required. -/
theorem tendsto_setIntegral_norm_criticalPotential_sub_neutral (α : ℝ) (s : Set ℝ) :
    Tendsto (fun ε : ℝ => ∫ t in s,
      ‖rayleighPotential α t (verticalCriticalSpeed ε) - neutralPotential α t‖)
      (𝓝[>] 0) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => norm_nonneg _)))
    ?_ (tendsto_integral_norm_criticalPotential_sub_neutral α)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact setIntegral_le_integral
    (integrable_rayleighPotential_sub_neutral_vertical α hε).norm
    (ae_of_all _ (fun _ => norm_nonneg _))

end UnforcedLeray.Rayleigh.Evans
