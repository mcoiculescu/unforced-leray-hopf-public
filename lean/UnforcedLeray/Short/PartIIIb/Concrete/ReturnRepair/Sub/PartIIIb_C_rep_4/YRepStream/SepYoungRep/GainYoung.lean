import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps
import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import UnforcedLeray.Short.PartIIIa.Defs

/-!
# Gain weight on the young body region `{ν s ≤ 1}` (source 2683-2689, 3875, 5117)

On the set `{p | ν * p.1 ≤ 1}` the body density `π ginv²` of `bodyMeasure` is bounded by
`π exp(2|γ|/ν)`: with `m = max s 0`, `0 ≤ m`, `ν m ≤ 1`, and
`|γ m /(1 + ν m)| ≤ |γ| m ≤ |γ|/ν`, so `ginv = exp(-(γ m/(1+ν m)))` obeys `ginv ≤ exp(|γ|/ν)`.
-/

set_option autoImplicit false

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Exponent bound: for `0 ≤ m` with `ν m ≤ 1`, `exp(-(γ m/(1+ν m)))² ≤ exp(2|γ|/ν)`. -/
lemma exp_neg_sq_le_aux (γ ν m : ℝ) (hν : 0 < ν) (hm0 : 0 ≤ m) (hνm : ν * m ≤ 1) :
    Real.exp (-(γ * m / (1 + ν * m))) ^ 2 ≤ Real.exp (2 * |γ| / ν) := by
  have hpos : 0 < 1 + ν * m := by nlinarith [mul_nonneg hν.le hm0]
  have hden : 1 ≤ 1 + ν * m := by nlinarith [mul_nonneg hν.le hm0]
  have ht : |γ * m / (1 + ν * m)| ≤ |γ| / ν := by
    rw [abs_div, abs_mul, abs_of_nonneg hm0, abs_of_pos hpos]
    refine le_trans (div_le_self (mul_nonneg (abs_nonneg γ) hm0) hden) ?_
    rw [le_div_iff₀ hν]
    nlinarith [abs_nonneg γ, mul_le_mul_of_nonneg_left hνm (abs_nonneg γ)]
  have h1 : -(γ * m / (1 + ν * m)) ≤ |γ| / ν := le_trans (neg_le_abs _) ht
  have h2 : Real.exp (-(γ * m / (1 + ν * m))) ≤ Real.exp (|γ| / ν) := Real.exp_le_exp.mpr h1
  have h3 : Real.exp (-(γ * m / (1 + ν * m))) ^ 2 ≤ Real.exp (|γ| / ν) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h2 2
  have h4 : Real.exp (|γ| / ν) ^ 2 = Real.exp (2 * |γ| / ν) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h4] at h3
  exact h3

/-- On `{ν s ≤ 1}` the squared inverse gain is at most `exp(2|γ|/ν)`. -/
lemma ginv_sq_le_of_nu_mul_le (γ ν : ℝ) (hν : 0 < ν) (p : Chart) (hp : ν * p.1 ≤ 1) :
    ginv γ ν p ^ 2 ≤ Real.exp (2 * |γ| / ν) := by
  have hm0 : 0 ≤ max p.1 0 := le_max_right _ _
  have hνm : ν * max p.1 0 ≤ 1 := by
    rcases le_total 0 p.1 with h | h
    · rw [max_eq_left h]
      exact hp
    · rw [max_eq_right h, mul_zero]
      exact zero_le_one
  have hE : ginv γ ν p = Real.exp (-(γ * max p.1 0 / (1 + ν * max p.1 0))) := by
    simp only [ginv, UnforcedLeray.Short.IIIa.gainG, Real.exp_neg]
  rw [hE]
  exact exp_neg_sq_le_aux γ ν (max p.1 0) hν hm0 hνm

/-- The inverse gain is measurable on the chart. -/
lemma measurable_ginv_chart (γ ν : ℝ) : Measurable (ginv γ ν) := by
  have h1 : Measurable fun p : Chart => max p.1 0 := measurable_fst.max measurable_const
  have h2 : Measurable fun p : Chart => γ * max p.1 0 / (1 + ν * max p.1 0) :=
    (measurable_const.mul h1).div (measurable_const.add (measurable_const.mul h1))
  have h3 : Measurable fun p : Chart => UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) :=
    Real.continuous_exp.measurable.comp h2
  exact h3.inv

theorem bodyMeasure_young_le (c γ ν : ℝ) (hν : 0 < ν) (f : Chart → ℝ≥0∞) : ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, f p ∂(bodyMeasure c γ ν) ≤ ENNReal.ofReal (Real.pi * Real.exp (2 * |γ| / ν)) * ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, f p ∂(ageμ c (-3 / 2)) := by
  have hf : Measurable fun p : Chart => ν * p.1 := by fun_prop
  have hSm : MeasurableSet {p : Chart | ν * p.1 ≤ 1} := measurableSet_le hf measurable_const
  have hdens : Measurable fun p : Chart => ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) :=
    (measurable_const.mul ((measurable_ginv_chart γ ν).pow_const 2)).ennreal_ofReal
  have hbd : ∀ p ∈ {p : Chart | ν * p.1 ≤ 1},
      ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) ≤ ENNReal.ofReal (Real.pi * Real.exp (2 * |γ| / ν)) := by
    intro p hp
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (ginv_sq_le_of_nu_mul_le γ ν hν p hp) Real.pi_pos.le)
  rw [bodyMeasure, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hdens f hSm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine le_trans (setLIntegral_mono' hSm (fun p hp => by
      show ENNReal.ofReal (Real.pi * ginv γ ν p ^ 2) * f p
        ≤ ENNReal.ofReal (Real.pi * Real.exp (2 * |γ| / ν)) * f p
      gcongr
      exact ginv_sq_le_of_nu_mul_le γ ν hν p hp)) ?_
  exact le_of_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end UnforcedLeray.Short.PartIIIb.Concrete
