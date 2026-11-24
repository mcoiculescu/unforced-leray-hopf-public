import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Quartic line integral `∫_ℝ (a² + t²)^{-2} dt = (π/2) a^{-3}` (`PartIII-b:C/near/masked/14/2/3/2/1/1`)

Source: the `z₂`-integral in `SchurOne` (source 3996-4011). Substitution `t = a u` reduces it to
`∫_ℝ (1+u²)^{-2} du = π/2`, which is the derivative of `G u = (u/(1+u²) + arctan u)/2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb

theorem quarticLine_pow_neg_two (x : ℝ) (hx : 0 ≤ x) : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_two]

theorem quarticLine_pow_neg_four (x : ℝ) (hx : 0 ≤ x) : x ^ (-4 : ℝ) = (x ^ 4)⁻¹ := by
  rw [Real.rpow_neg hx, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem quarticLine_pow_neg_three (x : ℝ) (hx : 0 ≤ x) : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
  rw [Real.rpow_neg hx, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem quarticLine_integrable : Integrable (fun u : ℝ => (1 + u ^ 2) ^ (-2 : ℝ)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (μ := volume) (E := ℝ) (r := 4) (by norm_num)
  refine h.congr (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [Real.norm_eq_abs, sq_abs]
  norm_num

theorem quarticLine_integral : ∫ u : ℝ, (1 + u ^ 2) ^ (-2 : ℝ) = Real.pi / 2 := by
  have hrw : ∀ u : ℝ, (1 + u ^ 2) ^ (-2 : ℝ) = ((1 + u ^ 2) ^ 2)⁻¹ := fun u =>
    quarticLine_pow_neg_two _ (by positivity)
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => (u / (1 + u ^ 2) + Real.arctan u) / 2)
      ((1 + u ^ 2) ^ (-2 : ℝ)) u := by
    intro u
    have hne : (1 + u ^ 2) ≠ 0 := by positivity
    have h1 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * u) u := by
      simpa using (hasDerivAt_pow 2 u).const_add 1
    have h2 : HasDerivAt (fun u : ℝ => u / (1 + u ^ 2))
        ((1 * (1 + u ^ 2) - u * (2 * u)) / (1 + u ^ 2) ^ 2) u :=
      (hasDerivAt_id' u).div h1 hne
    have h3 : HasDerivAt (fun u : ℝ => Real.arctan u) (1 / (1 + u ^ 2)) u :=
      Real.hasDerivAt_arctan u
    have h4 := (h2.add h3).div_const 2
    refine HasDerivAt.congr_deriv h4 ?_
    rw [hrw u]
    field_simp
    ring
  -- `u/(1+u²) → 0` at `+∞`, squeezed by `u⁻¹`
  have h0top : Tendsto (fun u : ℝ => u / (1 + u ^ 2)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
      exact div_nonneg hu (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hu0 : 0 < u := by linarith
      have hne : u ≠ 0 := hu0.ne'
      calc u / (1 + u ^ 2) ≤ u / u ^ 2 :=
            div_le_div_of_nonneg_left hu0.le (pow_pos hu0 2) (by nlinarith)
        _ = u⁻¹ := by field_simp
  have h0bot : Tendsto (fun u : ℝ => u / (1 + u ^ 2)) atBot (𝓝 0) := by
    have h := (h0top.comp tendsto_neg_atBot_atTop).neg
    rw [neg_zero] at h
    convert h using 2 with u
    simp only [Function.comp_apply, neg_sq]
    ring
  have htop : Tendsto (fun u : ℝ => (u / (1 + u ^ 2) + Real.arctan u) / 2) atTop
      (𝓝 (Real.pi / 4)) := by
    have h := ((h0top.add (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds)).div_const 2)
    convert h using 2
    ring
  have hbot : Tendsto (fun u : ℝ => (u / (1 + u ^ 2) + Real.arctan u) / 2) atBot
      (𝓝 (-(Real.pi / 4))) := by
    have h := ((h0bot.add (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds)).div_const 2)
    convert h using 2
    ring
  have key := integral_of_hasDerivAt_of_tendsto hderiv quarticLine_integrable hbot htop
  rw [key]
  ring

theorem lintegral_quartic_line (a : ℝ) (ha : 0 < a) : ∫⁻ t : ℝ, ENNReal.ofReal ((a ^ 2 + t ^ 2) ^ (-2 : ℝ)) = ENNReal.ofReal (Real.pi / 2 * a ^ (-3 : ℝ)) := by
  have ha' : a ≠ 0 := ha.ne'
  have hf_eq : ∀ t : ℝ, (a ^ 2 + t ^ 2) ^ (-2 : ℝ) = a ^ (-4 : ℝ) * (1 + (t / a) ^ 2) ^ (-2 : ℝ) := by
    intro t
    have hp1 : (0 : ℝ) ≤ a ^ 2 + t ^ 2 := by positivity
    have hp2 : (0 : ℝ) ≤ 1 + (t / a) ^ 2 := by positivity
    rw [quarticLine_pow_neg_two _ hp1, quarticLine_pow_neg_four a ha.le, quarticLine_pow_neg_two _ hp2]
    have hpos : a ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp
  have hfun : (fun t : ℝ => (a ^ 2 + t ^ 2) ^ (-2 : ℝ))
      = fun t : ℝ => a ^ (-4 : ℝ) * (1 + (t / a) ^ 2) ^ (-2 : ℝ) := funext hf_eq
  have hfI : Integrable (fun t : ℝ => (a ^ 2 + t ^ 2) ^ (-2 : ℝ)) := by
    rw [hfun]
    exact (quarticLine_integrable.comp_div ha').const_mul _
  have hnn : 0 ≤ᵐ[volume] (fun t : ℝ => (a ^ 2 + t ^ 2) ^ (-2 : ℝ)) :=
    Eventually.of_forall fun t => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hfI hnn]
  congr 1
  have hc := Measure.integral_comp_div (fun u : ℝ => (1 + u ^ 2) ^ (-2 : ℝ)) a
  rw [hfun, integral_const_mul, hc, quarticLine_integral, smul_eq_mul, abs_of_pos ha,
    quarticLine_pow_neg_four a ha.le, quarticLine_pow_neg_three a ha.le]
  field_simp
