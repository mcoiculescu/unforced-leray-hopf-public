import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussPointBound
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-!


Source `the November 2 reference manuscript`
lines 4569-4570.

Route: polar coordinates on `ℝ × ℝ` (`integral_comp_polarCoord_symm`, no integrability needed),
then the target `Ioi 0 ×ˢ Ioo (-π) π` splits as a product (`setIntegral_prod_mul`, no integrability
needed).  For `hMode`, the angular factor is `exp(2iθ)`, whose integral over `(-π, π)` is zero.
For `rMode`, the radial factor is `r (rE' + 2E)`, and `∫_0^∞ r (rE' + 2E) dr = [r² E]_0^∞ = 0`
(`integral_Ioi_of_hasDerivAt_of_tendsto`; integrability by the explicit form
`E' r + 2E = a⁻² e^{-r²/(4a)}(4 - 3r²/a + r⁴/(4a²))`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pz_symm (p : ℝ × ℝ) : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl

theorem pz_target : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi := rfl

theorem pz_planeR_polar (r θ : ℝ) (hr : 0 < r) :
    planeR (r * Real.cos θ, r * Real.sin θ) = r := by
  have hreal : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ
  show Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r
  rw [hreal, Real.sqrt_sq hr.le]

theorem pz_angTwo_polar (r θ : ℝ) (hr : 0 < r) :
    IIIa.angTwo (r * Real.cos θ, r * Real.sin θ) = Complex.exp (2 * Complex.I * (θ : ℂ)) := by
  have hreal : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz : ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I
      = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hd : (((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 : ℝ) : ℂ) = (r : ℂ) ^ 2 := by
    rw [hreal]
    push_cast
    ring
  show (((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I) ^ 2 /
      (((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 : ℝ) : ℂ) = _
  rw [hz, hd, mul_pow, ← Complex.exp_nat_mul, mul_div_cancel_left₀ _ (pow_ne_zero 2 hr0)]
  congr 1
  push_cast
  ring

theorem pz_ang_integral :
    ∫ θ in Ioo (-Real.pi) Real.pi, Complex.exp (2 * Complex.I * (θ : ℂ)) = 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rw [integral_exp_mul_complex (c := 2 * Complex.I) (by simp)]
  have h1 : Complex.exp (2 * Complex.I * (Real.pi : ℂ)) = 1 := by
    rw [show 2 * Complex.I * (Real.pi : ℂ) = 2 * Real.pi * Complex.I by ring]
    exact Complex.exp_two_pi_mul_I
  have h2 : Complex.exp (2 * Complex.I * ((-Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show 2 * Complex.I * ((-Real.pi : ℝ) : ℂ) = -(2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  rw [h1, h2, sub_self, zero_div]

/-- The radial integral `∫_0^∞ r (rE' + 2E) dr = 0` (source 4569-4570). -/
theorem pz_radial (a : ℝ) (ha : 1 ≤ a) :
    ∫ r in Ioi (0 : ℝ), r * (gaussRdE a r + 2 * gaussE a r) = 0 := by
  have hpos : (0 : ℝ) < a := by linarith
  have ha0 : a ≠ 0 := hpos.ne'
  -- derivative of `r² E(r)`
  have hGd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => r ^ 2 * gaussE a r)
      (r * (gaussRdE a r + 2 * gaussE a r)) r := by
    intro r
    have h1 := (hasDerivAt_pow 2 r).mul (gaussE_hasDerivAt a r ha0)
    refine h1.congr_deriv ?_
    rw [gaussRdE_eq a r ha0]
    unfold gaussE
    norm_num
    field_simp
    ring
  have hGc : Continuous (fun r : ℝ => r ^ 2 * gaussE a r) :=
    continuous_iff_continuousAt.2 fun r =>
      ((hasDerivAt_pow 2 r).mul (gaussE_hasDerivAt a r ha0)).continuousAt
  -- integrability of the integrand on `(0, ∞)`
  have hint : IntegrableOn (fun r : ℝ => r * (gaussRdE a r + 2 * gaussE a r)) (Ioi 0) := by
    have hb : (0 : ℝ) < 1 / (4 * a) := by positivity
    have i1 := integrable_rpow_mul_exp_neg_mul_sq hb (s := 1) (by norm_num)
    have i3 := integrable_rpow_mul_exp_neg_mul_sq hb (s := 3) (by norm_num)
    have i5 := integrable_rpow_mul_exp_neg_mul_sq hb (s := 5) (by norm_num)
    have combAll := ((((i1.const_mul 4).sub (i3.const_mul (3 / a))).add
      (i5.const_mul (1 / (4 * a ^ 2)))).const_mul ((a ^ 2)⁻¹))
    have comb : IntegrableOn (fun x : ℝ => (a ^ 2)⁻¹ * (4 * (x ^ (1 : ℝ) *
        Real.exp (-(1 / (4 * a)) * x ^ 2)) - 3 / a * (x ^ (3 : ℝ) *
        Real.exp (-(1 / (4 * a)) * x ^ 2)) + 1 / (4 * a ^ 2) * (x ^ (5 : ℝ) *
        Real.exp (-(1 / (4 * a)) * x ^ 2)))) (Ioi 0) := by
      exact combAll.integrableOn
    refine IntegrableOn.congr_fun comb ?_ measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only
    have e1 : r ^ (1 : ℝ) = r := Real.rpow_one r
    have e3 : r ^ (3 : ℝ) = r ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e5 : r ^ (5 : ℝ) = r ^ 5 := by
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e1, e3, e5, gaussRdE_eq a r ha0]
    unfold gaussE
    rw [show Real.exp (-(r ^ 2) / (4 * a)) = Real.exp (-(1 / (4 * a)) * r ^ 2) by
      congr 1; ring]
    field_simp
    ring
  -- the antiderivative vanishes at `0` and at `∞`
  have hlim : Tendsto (fun r : ℝ => r ^ 2 * gaussE a r) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun r : ℝ => r ^ 2 / (4 * a)) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const (by linarith)
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have h3 := ((h1.sub h2).const_mul (8 / a)).comp hcomp
    refine Tendsto.congr (fun r => ?_) (by simpa using h3)
    simp only [Function.comp_apply, gaussE]
    simp only [neg_div]
    field_simp
    ring
  have hfund := integral_Ioi_of_hasDerivAt_of_tendsto hGc.continuousWithinAt
    (fun r _ => hGd r) hint hlim
  exact hfund.trans (by simp)

theorem hMode_polar_eq (a : ℝ) (p : ℝ × ℝ) (hr : 0 < p.1) :
    p.1 • hMode a (polarCoord.symm p)
      = ((p.1 * gaussRdE a p.1 : ℝ) : ℂ) * Complex.exp (2 * Complex.I * (p.2 : ℂ)) := by
  rw [pz_symm]
  unfold hMode
  rw [pz_planeR_polar p.1 p.2 hr, pz_angTwo_polar p.1 p.2 hr, Complex.real_smul]
  push_cast
  ring

/-- **Zero plane integrals of the source profiles** (source 4569-4570). -/
theorem planeZero : PlaneZero := by
  intro a ha
  have hpos : (0 : ℝ) < a := by linarith
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  constructor
  · -- angular mode
    have h := integral_comp_polarCoord_symm (E := ℂ) (fun x : ℝ × ℝ => hMode a x)
    beta_reduce at h
    have hc1 : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi, p.1 • hMode a (polarCoord.symm p)
        = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          (fun r : ℝ => ((r * gaussRdE a r : ℝ) : ℂ)) p.1 *
            (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ))) p.2 :=
      setIntegral_congr_fun hmeas (fun p hp => by
        have hr : 0 < p.1 := hp.1
        exact hMode_polar_eq a p hr)
    rw [← h, pz_target, hc1, Measure.volume_eq_prod,
      setIntegral_prod_mul (fun r : ℝ => ((r * gaussRdE a r : ℝ) : ℂ))
        (fun θ : ℝ => Complex.exp (2 * Complex.I * (θ : ℂ)))]
    simp only [pz_ang_integral, mul_zero]
  · -- radial mode
    have hc2 : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • (gaussRdE a (planeR (polarCoord.symm p)) + 2 * gaussE a (planeR (polarCoord.symm p)))
        = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          (fun r : ℝ => r * (gaussRdE a r + 2 * gaussE a r)) p.1 * (fun _ : ℝ => (1 : ℝ)) p.2 :=
      setIntegral_congr_fun hmeas (fun p hp => by
        have hr : 0 < p.1 := hp.1
        show p.1 * (gaussRdE a (planeR (polarCoord.symm p)) + 2 * gaussE a (planeR (polarCoord.symm p)))
          = p.1 * (gaussRdE a p.1 + 2 * gaussE a p.1) * 1
        rw [pz_symm, pz_planeR_polar p.1 p.2 hr]
        ring)
    have hRint : ∫ x : ℝ × ℝ, (gaussRdE a (planeR x) + 2 * gaussE a (planeR x)) = 0 := by
      have h := integral_comp_polarCoord_symm (E := ℝ)
        (fun x : ℝ × ℝ => gaussRdE a (planeR x) + 2 * gaussE a (planeR x))
      beta_reduce at h
      rw [← h, pz_target, hc2, Measure.volume_eq_prod,
        setIntegral_prod_mul (fun r : ℝ => r * (gaussRdE a r + 2 * gaussE a r))
          (fun _ : ℝ => (1 : ℝ))]
      simp only [pz_radial a ha, zero_mul]
    have hconv : ∫ x : ℝ × ℝ, rMode a x
        = ((∫ x : ℝ × ℝ, (gaussRdE a (planeR x) + 2 * gaussE a (planeR x)) : ℝ) : ℂ) := by
      exact integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure (ℝ × ℝ)))
        (f := fun x : ℝ × ℝ => gaussRdE a (planeR x) + 2 * gaussE a (planeR x))
    rw [hconv, hRint, Complex.ofReal_zero]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
