import UnforcedLeray.Analysis.Rayleigh.SpeedBound
import UnforcedLeray.Analysis.Rayleigh.WeakExtractionPairings

/-!
# The genuine Gaussian equation in the whole-line weak limit

Zero extension preserves the undivided algebraic Rayleigh equation pointwise.
The actual coefficients Ω and A are bounded, so multiplication by either sends
L² tests into L². Full complex weak pairing convergence and convergence of the
speeds therefore pass the equation to the limit. Testing its L² residual against
its own conjugate proves the actual almost-everywhere identity. No division by
the limiting spectral denominator is made, and no lower bound on Im c is used.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace UnforcedLeray.Rayleigh
open Sturm GaussianPotential

/-- The actual undivided logarithmic Gaussian Rayleigh expression. -/
def undividedResidual (c : ℂ) (f k : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((neutralOmega t : ℂ) - c) * k t - (gaussianRayleighCoefficient t : ℂ) * f t

theorem continuous_gaussianRayleighCoefficient : Continuous gaussianRayleighCoefficient := by
  rw [show gaussianRayleighCoefficient =
      (fun t => 4 * neutralRadius t * (neutralRadius t - 2) * neutralOmega t) from
    funext gaussianRayleighCoefficient_eq]
  exact ((continuous_neutralRadius.const_mul 4).fun_mul
    (continuous_neutralRadius.sub continuous_const)).fun_mul continuous_neutralOmega

theorem abs_neutralOmega_le_one (t : ℝ) : |neutralOmega t| ≤ 1 := by
  rw [abs_of_pos (neutralOmega_pos t)]
  exact (neutralOmega_lt_one t).le

theorem abs_gaussianRayleighCoefficient_le_eight (t : ℝ) :
    |gaussianRayleighCoefficient t| ≤ 8 := by
  have hb : |gaussianOffset t| ≤ 1 := by
    have hs := gaussianOffset_sq_le_one t
    nlinarith [sq_abs (gaussianOffset t), abs_nonneg (gaussianOffset t)]
  rw [gaussianRayleighCoefficient, abs_mul, abs_neg, abs_of_pos (Wlog_pos t)]
  calc
    Wlog t * |gaussianOffset t| ≤ Wlog t * 1 :=
      mul_le_mul_of_nonneg_left hb (Wlog_pos t).le
    _ = Wlog t := mul_one _
    _ ≤ 8 := Wlog_le_eight t

/-- Multiplication by an actual continuous bounded real coefficient preserves L². -/
theorem memLp_realCoefficient_mul (a : ℝ → ℝ) (ha : Continuous a)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, |a t| ≤ C)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun t => (a t : ℂ) * f t) 2 volume := by
  apply (hf.const_mul (C : ℂ)).mono
    (((Complex.continuous_ofReal.comp ha).aestronglyMeasurable).fun_mul
      hf.aestronglyMeasurable)
  filter_upwards [] with t
  simp only [Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _)

theorem memLp_neutralOmega_mul {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun t => (neutralOmega t : ℂ) * f t) 2 volume :=
  memLp_realCoefficient_mul neutralOmega continuous_neutralOmega 1 (by norm_num)
    abs_neutralOmega_le_one hf

theorem memLp_gaussianRayleighCoefficient_mul {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (fun t => (gaussianRayleighCoefficient t : ℂ) * f t) 2 volume :=
  memLp_realCoefficient_mul gaussianRayleighCoefficient
    continuous_gaussianRayleighCoefficient 8 (by norm_num)
    abs_gaussianRayleighCoefficient_le_eight hf

/-- The full limiting algebraic residual is a genuine L² function. -/
theorem memLp_undividedResidual (c : ℂ) {f k : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hk : MemLp k 2 volume) :
    MemLp (undividedResidual c f k) 2 volume := by
  have he : undividedResidual c f k =
      ((fun t => (neutralOmega t : ℂ) * k t) - (fun t => c * k t)) -
        (fun t => (gaussianRayleighCoefficient t : ℂ) * f t) := by
    funext t
    simp only [undividedResidual, Pi.sub_apply]
    ring
  rw [he]
  exact ((memLp_neutralOmega_mul hk).sub (hk.const_mul c)).sub
    (memLp_gaussianRayleighCoefficient_mul hf)

/-- All test pairings split as ordinary convergent integrals, by L² Hölder. -/
theorem integral_undividedResidual_mul (c : ℂ) (f k : ComplexL2)
    (ψ : ℝ → ℂ) (hψ : MemLp ψ 2 volume) :
    (∫ t, undividedResidual c f k t * ψ t) =
      (∫ t, k t * ((neutralOmega t : ℂ) * ψ t)) -
      c * (∫ t, k t * ψ t) -
      (∫ t, f t * ((gaussianRayleighCoefficient t : ℂ) * ψ t)) := by
  have hO := integrable_mul_l2 _ (memLp_neutralOmega_mul hψ) k
  have hk := integrable_mul_l2 ψ hψ k
  have hA := integrable_mul_l2 _ (memLp_gaussianRayleighCoefficient_mul hψ) f
  have hsub : Integrable (fun t => k t * ((neutralOmega t : ℂ) * ψ t) -
      c * (k t * ψ t)) volume := hO.sub (hk.const_mul c)
  calc
    _ = ∫ t, (k t * ((neutralOmega t : ℂ) * ψ t) - c * (k t * ψ t)) -
          f t * ((gaussianRayleighCoefficient t : ℂ) * ψ t) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by unfold undividedResidual; ring
    _ = _ := by
      rw [integral_sub hsub hA,
        integral_sub hO (hk.const_mul c), integral_const_mul]

namespace GaussianAnnularMode
variable {c : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : GaussianAnnularMode c F l r)
include h

/-- Both zero extensions vanish off the annulus, so the undivided equation
holds there too, without discarding any second-derivative jump. -/
theorem zeroExtension_undivided_equation (t : ℝ) :
    undividedResidual c (zeroExtension l r F)
      (zeroExtension l r (fun x => deriv (deriv F) x - 4 * F x)) t = 0 := by
  by_cases ht : t ∈ Ioc l r
  · simpa only [undividedResidual, zeroExtension, indicator_of_mem ht] using h.equation t ht
  · simp only [undividedResidual, zeroExtension, indicator_of_notMem ht, mul_zero, sub_zero]

/-- The actual L² representatives carry the same equation almost everywhere. -/
theorem class_undivided_equation :
    undividedResidual c h.toShifted.fieldL2 h.toShifted.residualL2 =ᵐ[volume] 0 := by
  filter_upwards [h.toShifted.coeFn_fieldL2, h.toShifted.coeFn_residualL2] with t hf hk
  change undividedResidual c h.toShifted.fieldL2 h.toShifted.residualL2 t = 0
  simpa only [undividedResidual, hf, hk] using h.zeroExtension_undivided_equation t

/-- The exact integrated equation for every L² test, not only compact tests. -/
theorem integral_undivided_equation (ψ : ℝ → ℂ) (hψ : MemLp ψ 2 volume) :
    (∫ t, h.toShifted.residualL2 t * ((neutralOmega t : ℂ) * ψ t)) -
      c * (∫ t, h.toShifted.residualL2 t * ψ t) -
      (∫ t, h.toShifted.fieldL2 t * ((gaussianRayleighCoefficient t : ℂ) * ψ t)) = 0 := by
  rw [← integral_undividedResidual_mul c h.toShifted.fieldL2 h.toShifted.residualL2 ψ hψ]
  apply integral_eq_zero_of_ae
  filter_upwards [h.class_undivided_equation] with t ht
  change undividedResidual c h.toShifted.fieldL2 h.toShifted.residualL2 t * ψ t = 0
  simp only [ht, Pi.zero_apply, zero_mul]

end GaussianAnnularMode

/-- Full complex pairing convergence passes the actual equation to the limit
without dividing by the potentially real limiting spectral denominator. -/
theorem integral_undivided_equation_of_weak_limits
    {c : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    (h : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n))
    {cLimit : ℂ} (hc : Tendsto c atTop (𝓝 cLimit)) {f k : ComplexL2}
    (hf : WeakL2.WeakTendsto (fun n => (h n).toShifted.fieldL2) atTop f)
    (hk : WeakL2.WeakTendsto (fun n => (h n).toShifted.residualL2) atTop k)
    (ψ : ℝ → ℂ) (hψ : MemLp ψ 2 volume) :
    (∫ t, undividedResidual cLimit f k t * ψ t) = 0 := by
  have hO := weakTendsto_integral_mul hk _ (memLp_neutralOmega_mul hψ)
  have hK := weakTendsto_integral_mul hk ψ hψ
  have hA := weakTendsto_integral_mul hf _ (memLp_gaussianRayleighCoefficient_mul hψ)
  have hlim := (hO.sub (hc.mul hK)).sub hA
  have hzero : Tendsto
      (fun n => (∫ t, (h n).toShifted.residualL2 t * ((neutralOmega t : ℂ) * ψ t)) -
        c n * (∫ t, (h n).toShifted.residualL2 t * ψ t) -
        (∫ t, (h n).toShifted.fieldL2 t * ((gaussianRayleighCoefficient t : ℂ) * ψ t)))
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n => ((h n).integral_undivided_equation ψ hψ).symm
  rw [integral_undividedResidual_mul cLimit f k ψ hψ]
  exact tendsto_nhds_unique hlim hzero

/-- The whole-line limit satisfies the actual undivided Gaussian Rayleigh
equation almost everywhere. The L² residual is tested against its own conjugate. -/
theorem gaussian_equation_of_weak_limits
    {c : ℕ → ℂ} {F : ℕ → ℝ → ℂ} {l r : ℕ → ℝ}
    (h : ∀ n, GaussianAnnularMode (c n) (F n) (l n) (r n))
    {cLimit : ℂ} (hc : Tendsto c atTop (𝓝 cLimit)) {f k : ComplexL2}
    (hf : WeakL2.WeakTendsto (fun n => (h n).toShifted.fieldL2) atTop f)
    (hk : WeakL2.WeakTendsto (fun n => (h n).toShifted.residualL2) atTop k) :
    ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - cLimit) * k t -
        (gaussianRayleighCoefficient t : ℂ) * f t = 0 := by
  let g : ℝ → ℂ := undividedResidual cLimit f k
  have hg : MemLp g 2 volume := memLp_undividedResidual cLimit (Lp.memLp f) (Lp.memLp k)
  have hz := integral_undivided_equation_of_weak_limits h hc hf hk (star g) hg.star
  have hre := congrArg Complex.re hz
  change (∫ t, (g * star g) t).re = 0 at hre
  have hi : (∫ t, ((g * star g) t).re) = 0 :=
    (integral_re (hg.integrable_mul hg.star)).trans hre
  have hm : (∫ t, ‖g t‖ ^ 2) = 0 := by
    simpa only [Pi.mul_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hi
  have ha := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg ‖g t‖)
    (hg.integrable_norm_pow (by norm_num))).mp hm
  filter_upwards [ha] with t ht
  change g t = 0
  simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using ht

end UnforcedLeray.Rayleigh
