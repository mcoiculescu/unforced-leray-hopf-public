import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# `PartIII-b:C/rep/5/1/2/4/1/4/4/fiber`: the fibre integral of the stream kernel

Source `the November 2 reference manuscript` 5588-5591 (spatial `L²` norm of the
stream kernel on a horizontal line).  For `ρ > 0`:
`∫_ℝ ((ρ²(ρ²+x²))⁻¹)² dx = π/(2ρ⁷)`, by the antiderivative
`Ψ(x) = x/(2ρ⁶(ρ²+x²)) + arctan(x/ρ)/(2ρ⁷)` and `integral_of_hasDerivAt_of_tendsto`.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYStream

/-- The fibre integrand `((ρ²(ρ²+x²))⁻¹)²`. -/
def sfPhi (ρ x : ℝ) : ℝ := ((ρ ^ 2 * (ρ ^ 2 + x ^ 2))⁻¹) ^ 2

/-- An antiderivative of `sfPhi ρ`. -/
def sfPsi (ρ x : ℝ) : ℝ := x / (2 * ρ ^ 6 * (ρ ^ 2 + x ^ 2)) + Real.arctan (x / ρ) / (2 * ρ ^ 7)

theorem sfPsi_deriv (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) : HasDerivAt (sfPsi ρ) (sfPhi ρ x) x := by
  have hq : 0 < ρ ^ 2 + x ^ 2 := by positivity
  have hd : HasDerivAt (fun y : ℝ => 2 * ρ ^ 6 * (ρ ^ 2 + y ^ 2)) (2 * ρ ^ 6 * (2 * x)) x := by
    have h := (((hasDerivAt_pow 2 x).const_add (ρ ^ 2)).const_mul (2 * ρ ^ 6))
    exact h.congr_deriv (by norm_num)
  have h1 : HasDerivAt (fun y : ℝ => y / (2 * ρ ^ 6 * (ρ ^ 2 + y ^ 2)))
      ((1 * (2 * ρ ^ 6 * (ρ ^ 2 + x ^ 2)) - x * (2 * ρ ^ 6 * (2 * x))) /
        (2 * ρ ^ 6 * (ρ ^ 2 + x ^ 2)) ^ 2) x :=
    (hasDerivAt_id' x).div hd (by positivity)
  have hin : HasDerivAt (fun y : ℝ => y / ρ) (1 / ρ) x := by
    simpa using (hasDerivAt_id' x).div_const ρ
  have h2 : HasDerivAt (fun y : ℝ => Real.arctan (y / ρ))
      (1 / (1 + (x / ρ) ^ 2) * (1 / ρ)) x :=
    hin.arctan
  have h3 : HasDerivAt (fun y : ℝ => Real.arctan (y / ρ) / (2 * ρ ^ 7))
      (1 / (1 + (x / ρ) ^ 2) * (1 / ρ) / (2 * ρ ^ 7)) x :=
    h2.div_const _
  have h4 := h1.add h3
  exact h4.congr_deriv (by
    unfold sfPhi
    have hne : (1 + (x / ρ) ^ 2) ≠ 0 := by positivity
    have hρ' : ρ ≠ 0 := hρ.ne'
    have hq' : ρ ^ 2 + x ^ 2 ≠ 0 := hq.ne'
    field_simp
    ring)

theorem sfPsi_neg (ρ x : ℝ) : sfPsi ρ (-x) = -sfPsi ρ x := by
  unfold sfPsi
  simp only [neg_div, Real.arctan_neg, neg_sq]
  ring

theorem sfPsi_top (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (sfPsi ρ) atTop (𝓝 (Real.pi / (4 * ρ ^ 7))) := by
  have hA : Tendsto (fun x : ℝ => x / (2 * ρ ^ 6 * (ρ ^ 2 + x ^ 2))) atTop (𝓝 0) := by
    have hI : Tendsto (fun x : ℝ => (2 * ρ ^ 6)⁻¹ * x⁻¹) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.const_mul ((2 * ρ ^ 6)⁻¹)
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hI ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      apply div_nonneg hx.le
      positivity
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [div_le_iff₀ (by positivity)]
      have e : (2 * ρ ^ 6)⁻¹ * x⁻¹ * (2 * ρ ^ 6 * (ρ ^ 2 + x ^ 2)) = (ρ ^ 2 + x ^ 2) / x := by
        field_simp
      rw [e, le_div_iff₀ hx]
      nlinarith [sq_nonneg ρ]
  have hB : Tendsto (fun x : ℝ => Real.arctan (x / ρ) / (2 * ρ ^ 7)) atTop
      (𝓝 ((Real.pi / 2) / (2 * ρ ^ 7))) :=
    ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const hρ)).div_const _
  have hT := hA.add hB
  have e : Real.pi / (4 * ρ ^ 7) = 0 + (Real.pi / 2) / (2 * ρ ^ 7) := by
    field_simp
    ring
  rw [e]
  exact hT

theorem sfPsi_bot (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (sfPsi ρ) atBot (𝓝 (-(Real.pi / (4 * ρ ^ 7)))) := by
  have h := ((sfPsi_top ρ hρ).comp tendsto_neg_atBot_atTop).neg
  refine h.congr ?_
  intro x
  simp [Function.comp, sfPsi_neg]

theorem sfPhi_integrable (ρ : ℝ) (hρ : 0 < ρ) : Integrable (sfPhi ρ) := by
  set m : ℝ := min (ρ ^ 2) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  have hmle1 : m ≤ 1 := min_le_right _ _
  have hmleq : m ≤ ρ ^ 2 := min_le_left _ _
  have hg : Integrable (fun x : ℝ => (ρ ^ 2 * m)⁻¹ ^ 2 * (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine Integrable.mono' hg (by unfold sfPhi; fun_prop : Measurable (sfPhi ρ)).aestronglyMeasurable ?_
  refine Eventually.of_forall (fun x => ?_)
  have hx1 : 0 < 1 + x ^ 2 := by positivity
  have hsub : m * (1 + x ^ 2) ≤ ρ ^ 2 + x ^ 2 := by
    nlinarith [sq_nonneg x, mul_nonneg (sub_nonneg.2 hmle1) (sq_nonneg x)]
  have hnn : 0 ≤ sfPhi ρ x := by unfold sfPhi; positivity
  rw [Real.norm_of_nonneg hnn]
  have hA : ρ ^ 2 * (m * (1 + x ^ 2)) ≤ ρ ^ 2 * (ρ ^ 2 + x ^ 2) :=
    mul_le_mul_of_nonneg_left hsub (by positivity)
  have h1 : (ρ ^ 2 * (ρ ^ 2 + x ^ 2))⁻¹ ≤ (ρ ^ 2 * m)⁻¹ * (1 + x ^ 2)⁻¹ := by
    have hpos : 0 < ρ ^ 2 * (m * (1 + x ^ 2)) := by positivity
    calc (ρ ^ 2 * (ρ ^ 2 + x ^ 2))⁻¹ ≤ (ρ ^ 2 * (m * (1 + x ^ 2)))⁻¹ := inv_anti₀ hpos hA
      _ = (ρ ^ 2 * m)⁻¹ * (1 + x ^ 2)⁻¹ := by rw [← mul_assoc, mul_inv]
  have hz0 : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hz1 : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
  have hC : 0 ≤ (ρ ^ 2 * m)⁻¹ := by positivity
  unfold sfPhi
  calc ((ρ ^ 2 * (ρ ^ 2 + x ^ 2))⁻¹) ^ 2
      ≤ ((ρ ^ 2 * m)⁻¹ * (1 + x ^ 2)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
    _ = (ρ ^ 2 * m)⁻¹ ^ 2 * ((1 + x ^ 2)⁻¹) ^ 2 := by ring
    _ ≤ (ρ ^ 2 * m)⁻¹ ^ 2 * (1 + x ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left (by nlinarith [hz0, hz1]) (sq_nonneg _)

theorem sfPhi_integral (ρ : ℝ) (hρ : 0 < ρ) : ∫ x, sfPhi ρ x = Real.pi / (2 * ρ ^ 7) := by
  have h := integral_of_hasDerivAt_of_tendsto (fun x => sfPsi_deriv ρ hρ x)
    (sfPhi_integrable ρ hρ) (sfPsi_bot ρ hρ) (sfPsi_top ρ hρ)
  rw [h]
  ring

/-- The shifted fibre integral `∫_ℝ ((ρ²(ρ²+(h-a)²))⁻¹)² dh = π/(2ρ⁷)`. -/
theorem sfPhi_shift_integral (ρ a : ℝ) (hρ : 0 < ρ) :
    ∫ h, sfPhi ρ (h - a) = Real.pi / (2 * ρ ^ 7) := by
  rw [integral_sub_right_eq_self (sfPhi ρ) a]
  exact sfPhi_integral ρ hρ

end UnforcedLeray.Short.PartIIIb.Concrete.WYStream

end
