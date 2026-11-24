import UnforcedLeray.Analysis.Rayleigh.GaussianMode
import UnforcedLeray.Analysis.Sturm.NeutralPotentialRegularity

/-!
# Actual Gaussian coefficients for the upper-half-plane Evans ODE

Dividing the concrete Rayleigh equation gives F''=V F, with
V=α²+A/(Ω−c). The imaginary part of c excludes every denominator zero.
All smoothness, joint continuity and holomorphy statements below concern
this actual Gaussian coefficient and are proved from its explicit formula.
-/

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedLeray.Rayleigh.Evans

/-- The open upper spectral half-plane. -/
def upperHalfPlane : Set ℂ := {c | 0 < c.im}

/-- The concrete second-order coefficient in the normalized Rayleigh ODE. -/
def rayleighPotential (α : ℝ) (t : ℝ) (c : ℂ) : ℂ :=
  (α : ℂ) ^ 2 + (gaussianRayleighCoefficient t : ℂ) / ((Sturm.neutralOmega t : ℂ) - c)

theorem isOpen_upperHalfPlane : IsOpen upperHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

theorem rayleighDenominator_ne_zero (t : ℝ) {c : ℂ} (hc : c ∈ upperHalfPlane) :
    (Sturm.neutralOmega t : ℂ) - c ≠ 0 :=
  criticalDenominator_ne_zero _ hc

theorem neutralOmega_smooth : ContDiff ℝ ∞ Sturm.neutralOmega := by
  unfold Sturm.neutralOmega Sturm.neutralRadius
  fun_prop

theorem gaussianRayleighCoefficient_smooth : ContDiff ℝ ∞ gaussianRayleighCoefficient := by
  unfold gaussianRayleighCoefficient gaussianOffset
  exact Sturm.Wlog_smooth.neg.mul (neutralOmega_smooth.sub contDiff_const)

/-- The divided coefficient is C∞ in logarithmic radius. -/
theorem rayleighPotential_smooth (α : ℝ) {c : ℂ} (hc : c ∈ upperHalfPlane) :
    ContDiff ℝ ∞ (fun t => rayleighPotential α t c) := by
  simp only [rayleighPotential, div_eq_mul_inv]
  exact contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp gaussianRayleighCoefficient_smooth).mul
      (((Complex.ofRealCLM.contDiff.comp neutralOmega_smooth).sub contDiff_const).inv
        (fun t => rayleighDenominator_ne_zero t hc)))

theorem continuous_rayleighPotential (α : ℝ) {c : ℂ} (hc : c ∈ upperHalfPlane) :
    Continuous (fun t => rayleighPotential α t c) :=
  (rayleighPotential_smooth α hc).continuous

/-- Joint continuity in logarithmic radius and spectral speed. -/
theorem continuousOn_rayleighPotential (α : ℝ) :
    ContinuousOn (fun q : ℝ × ℂ => rayleighPotential α q.1 q.2)
      (univ ×ˢ upperHalfPlane) := by
  have hA : Continuous (fun q : ℝ × ℂ => (gaussianRayleighCoefficient q.1 : ℂ)) :=
    Complex.continuous_ofReal.comp (gaussianRayleighCoefficient_smooth.continuous.comp continuous_fst)
  have hD : Continuous (fun q : ℝ × ℂ => (Sturm.neutralOmega q.1 : ℂ) - q.2) :=
    (Complex.continuous_ofReal.comp (neutralOmega_smooth.continuous.comp continuous_fst)).sub
      continuous_snd
  exact continuousOn_const.add (hA.continuousOn.div hD.continuousOn
    (fun q hq => rayleighDenominator_ne_zero q.1 hq.2))

/-- Holomorphy in the actual upper-half-plane spectral parameter. -/
theorem differentiableOn_rayleighPotential (α t : ℝ) :
    DifferentiableOn ℂ (rayleighPotential α t) upperHalfPlane := by
  intro c hc
  exact (differentiableAt_const ((α : ℂ) ^ 2)).add
    ((differentiableAt_const (gaussianRayleighCoefficient t : ℂ)).div
      ((differentiableAt_const (Sturm.neutralOmega t : ℂ)).sub (differentiableAt_id))
      (rayleighDenominator_ne_zero t hc)) |>.differentiableWithinAt

/-- Joint continuity in radius, real angular index and complex speed. -/
theorem continuousOn_rayleighPotential_parameters :
    ContinuousOn (fun q : ℝ × (ℝ × ℂ) => rayleighPotential q.2.1 q.1 q.2.2)
      (univ ×ˢ {p : ℝ × ℂ | p.2 ∈ upperHalfPlane}) := by
  have hα : Continuous (fun q : ℝ × (ℝ × ℂ) => (q.2.1 : ℂ) ^ 2) := by
    fun_prop
  have hA : Continuous (fun q : ℝ × (ℝ × ℂ) => (gaussianRayleighCoefficient q.1 : ℂ)) :=
    Complex.continuous_ofReal.comp (gaussianRayleighCoefficient_smooth.continuous.comp continuous_fst)
  have hD : Continuous (fun q : ℝ × (ℝ × ℂ) => (Sturm.neutralOmega q.1 : ℂ) - q.2.2) :=
    (Complex.continuous_ofReal.comp (neutralOmega_smooth.continuous.comp continuous_fst)).sub
      (continuous_snd.comp continuous_snd)
  exact hα.continuousOn.add (hA.continuousOn.div hD.continuousOn
    (fun q hq => rayleighDenominator_ne_zero q.1 hq.2))

/-- Explicit-name aliases for the normalized solution construction. -/
theorem upperHalfPlane_open : IsOpen upperHalfPlane := isOpen_upperHalfPlane

theorem rayleigh_denominator_ne_zero {c : ℂ} (hc : 0 < c.im) (t : ℝ) :
    (Sturm.neutralOmega t : ℂ) - c ≠ 0 := rayleighDenominator_ne_zero t hc

theorem contDiff_rayleighPotential (α : ℝ) {c : ℂ} (hc : 0 < c.im) :
    ContDiff ℝ ∞ (fun t => rayleighPotential α t c) := rayleighPotential_smooth α hc

end UnforcedLeray.Rayleigh.Evans
