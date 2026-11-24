import UnforcedLeray.Analysis.Rayleigh.Evans.CriticalCoefficientLimit

/-!
# The actual non-tangential critical-speed coefficient limit

A cone condition on the upper-half-plane spectral displacement bounds the exact
critical-layer remainder by a constant multiple of Wlog. Dominated convergence
then gives a genuine L¹ coefficient limit, on the whole line and on any annulus.
No solution limit or unstable-root existence is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace UnforcedLeray.Rayleigh.Evans
open Sturm GaussianPotential

/-- Displace the Gaussian critical speed by an actual complex increment. -/
def criticalShiftSpeed (δ : ℂ) : ℂ := (gaussianCriticalSpeed : ℂ) + δ

@[simp] theorem criticalShiftSpeed_im (δ : ℂ) : (criticalShiftSpeed δ).im = δ.im := by
  simp [criticalShiftSpeed]

@[simp] theorem criticalShiftSpeed_zero :
    criticalShiftSpeed 0 = (gaussianCriticalSpeed : ℂ) := by simp [criticalShiftSpeed]

/-- A closed-angle cone inside the upper half-plane, with its vertex removed. -/
def criticalApproachCone (C : ℝ) : Set ℂ := {δ | 0 < δ.im ∧ ‖δ‖ ≤ C * δ.im}

/-- Exact critical-layer remainder for every upper-half-plane displacement. -/
theorem rayleighPotential_sub_neutral_shifted (α t : ℝ) {δ : ℂ} (hδ : 0 < δ.im) :
    rayleighPotential α t (criticalShiftSpeed δ) - neutralPotential α t =
      -(Wlog t : ℂ) * δ / ((gaussianOffset t : ℂ) - δ) := by
  have hd : (gaussianOffset t : ℂ) - δ ≠ 0 := criticalDenominator_ne_zero _ hδ
  unfold rayleighPotential neutralPotential
  rw [gaussian_denominator_eq]
  simp only [shiftedSpeed, criticalShiftSpeed, add_sub_cancel_left,
    gaussianRayleighCoefficient, Complex.ofReal_neg, Complex.ofReal_mul]
  field_simp
  ring

/-- The cone controls the true singular remainder without a reciprocal
imaginary-speed loss. -/
theorem norm_rayleighPotential_sub_neutral_shifted_le (α t : ℝ) {C : ℝ}
    (hC : 0 ≤ C) {δ : ℂ} (hδ : δ ∈ criticalApproachCone C) :
    ‖rayleighPotential α t (criticalShiftSpeed δ) - neutralPotential α t‖ ≤ C * Wlog t := by
  rw [rayleighPotential_sub_neutral_shifted α t hδ.1, norm_div, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Wlog_pos t)]
  have hd : 0 < ‖(gaussianOffset t : ℂ) - δ‖ :=
    norm_pos_iff.mpr (criticalDenominator_ne_zero _ hδ.1)
  have hi : δ.im ≤ ‖(gaussianOffset t : ℂ) - δ‖ := by
    have h := Complex.abs_im_le_norm ((gaussianOffset t : ℂ) - δ)
    simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
      abs_of_pos hδ.1] using h
  apply (div_le_iff₀ hd).mpr
  have hmul := mul_le_mul_of_nonneg_left
    (hδ.2.trans (mul_le_mul_of_nonneg_left hi hC)) (Wlog_pos t).le
  nlinarith [hmul]

/-- The literal quotient has the completed neutral limit at every noncritical
log-radius. The single critical point is deliberately excluded here. -/
theorem tendsto_rayleighPotential_shifted_of_ne_critical (α : ℝ) {t : ℝ}
    (ht : t ≠ neutralCriticalTime) :
    Tendsto (fun δ : ℂ => rayleighPotential α t (criticalShiftSpeed δ))
      (𝓝 0) (𝓝 (neutralPotential α t)) := by
  have hd : (neutralOmega t : ℂ) - (gaussianCriticalSpeed : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_sub]
    exact_mod_cast gaussianOffset_ne_zero_off_critical ht
  have hc : ContinuousAt (fun δ : ℂ => rayleighPotential α t (criticalShiftSpeed δ)) 0 := by
    unfold rayleighPotential
    apply ContinuousAt.add continuousAt_const
    apply ContinuousAt.div continuousAt_const
    · unfold criticalShiftSpeed
      fun_prop
    · simpa using hd
  have he : rayleighPotential α t (criticalShiftSpeed 0) = neutralPotential α t := by
    simp only [criticalShiftSpeed_zero, rayleighPotential, neutralPotential,
      gaussianRayleighCoefficient, gaussianOffset, Complex.ofReal_neg,
      Complex.ofReal_mul, Complex.ofReal_sub]
    field_simp
    ring
  simpa only [he] using hc.tendsto

theorem integrable_rayleighPotential_sub_neutral_shifted (α : ℝ) {C : ℝ}
    (hC : 0 ≤ C) {δ : ℂ} (hδ : δ ∈ criticalApproachCone C) :
    Integrable (fun t => rayleighPotential α t (criticalShiftSpeed δ) - neutralPotential α t) := by
  have hc : Continuous (fun t => rayleighPotential α t (criticalShiftSpeed δ) -
      neutralPotential α t) :=
    (continuous_rayleighPotential α (by simpa [upperHalfPlane] using hδ.1)).sub
      (continuous_neutralPotential α)
  apply (integrable_Wlog.const_mul C).mono' hc.aestronglyMeasurable
  exact ae_of_all _ (fun t => norm_rayleighPotential_sub_neutral_shifted_le α t hC hδ)

/-- Genuine global L¹ convergence under the explicit approach-cone condition. -/
theorem tendsto_integral_norm_criticalPotential_sub_neutral_nontangential
    (α : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun δ : ℂ => ∫ t,
      ‖rayleighPotential α t (criticalShiftSpeed δ) - neutralPotential α t‖)
      (𝓝[criticalApproachCone C] 0) (𝓝 0) := by
  have hmeas : ∀ᶠ δ : ℂ in 𝓝[criticalApproachCone C] 0, AEStronglyMeasurable
      (fun t => ‖rayleighPotential α t (criticalShiftSpeed δ) -
        neutralPotential α t‖) volume := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (integrable_rayleighPotential_sub_neutral_shifted α hC hδ).norm.aestronglyMeasurable
  have hbound : ∀ᶠ δ : ℂ in 𝓝[criticalApproachCone C] 0, ∀ᵐ t : ℝ,
      ‖‖rayleighPotential α t (criticalShiftSpeed δ) - neutralPotential α t‖‖ ≤
        C * Wlog t := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ae_of_all _ (fun t => by
      simpa only [norm_norm] using norm_rayleighPotential_sub_neutral_shifted_le α t hC hδ)
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun δ : ℂ =>
      ‖rayleighPotential α t (criticalShiftSpeed δ) - neutralPotential α t‖)
      (𝓝[criticalApproachCone C] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [(volume : Measure ℝ).ae_ne neutralCriticalTime] with t ht
    have h := ((tendsto_rayleighPotential_shifted_of_ne_critical α ht).sub_const
      (neutralPotential α t)).norm
    simpa only [sub_self, norm_zero] using h.mono_left nhdsWithin_le_nhds
  simpa using tendsto_integral_filter_of_dominated_convergence (fun t => C * Wlog t)
    hmeas hbound (integrable_Wlog.const_mul C) hlim

/-- The same genuine limit on any annulus or other measurable integration region. -/
theorem tendsto_setIntegral_norm_criticalPotential_sub_neutral_nontangential
    (α : ℝ) (s : Set ℝ) {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun δ : ℂ => ∫ t in s,
      ‖rayleighPotential α t (criticalShiftSpeed δ) - neutralPotential α t‖)
      (𝓝[criticalApproachCone C] 0) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => norm_nonneg _)))
    ?_ (tendsto_integral_norm_criticalPotential_sub_neutral_nontangential α hC)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact setIntegral_le_integral (integrable_rayleighPotential_sub_neutral_shifted α hC hδ).norm
    (ae_of_all _ (fun _ => norm_nonneg _))

end UnforcedLeray.Rayleigh.Evans
