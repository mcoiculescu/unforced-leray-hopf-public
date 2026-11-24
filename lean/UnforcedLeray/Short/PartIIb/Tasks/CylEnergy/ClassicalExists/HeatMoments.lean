import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatMoments.Gauss1

/-!


Proves `HeatKernelMoments` (`Sub/T22_1/Stages.lean`). `heatK a (z₁, z₂) = K_a(z₁) K_a(z₂)` with
the one-dimensional normalized Gaussian `K_a` (helpers in `HeatMoments/Gauss1.lean`). Products of
one-dimensional integrable functions are integrable on the plane (`Integrable.mul_prod`,
`integral_prod_mul`), which reduces everything to the one-dimensional moments:
`∫K = 1`, `∫K cosh = e^a`, `∫|t|K = 4a/s`, and `∫|t| K cosh ≤ e^a (4a/s + 2a)` with `s = √(4πa)`.
The final bound uses `2/s ≤ a^{-1/2}` (from `s ≥ 2√a`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE

namespace HM

lemma prod_int {f g : ℝ → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun z : ℝ × ℝ => f z.1 * g z.2) ∧
      ∫ z : ℝ × ℝ, f z.1 * g z.2 = (∫ t, f t) * ∫ t, g t := by
  refine ⟨?_, ?_⟩
  · have := hf.mul_prod hg
    rwa [← Measure.volume_eq_prod] at this
  · rw [Measure.volume_eq_prod, integral_prod_mul]

lemma heatK_pos {a : ℝ} (ha : 0 < a) (z : Pl) : 0 < heatK a z := by
  unfold heatK
  positivity

lemma integrable_absKK {a : ℝ} (ha : 0 < a) : Integrable (fun t : ℝ => |t| * KK a t) := by
  have e : (fun t : ℝ => |t| * KK a t) =
      fun t : ℝ => (ss a)⁻¹ * (|t| * Real.exp (-(bb a) * t ^ 2)) := by
    funext t; unfold KK; ring
  rw [e]
  exact (integrable_abs_mul_gauss ha).const_mul _

lemma two_div_ss_le {a : ℝ} (ha : 0 < a) : 2 / ss a ≤ a ^ (-(1 / 2 : ℝ)) := by
  have hr : a ^ (-(1 / 2 : ℝ)) = (Real.sqrt a)⁻¹ := by
    rw [Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
  have hr0 : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr0' : Real.sqrt a ≠ 0 := hr0.ne'
  have hpi : 0 ≤ a * (Real.pi - 1) := mul_nonneg ha.le (by linarith [Real.pi_gt_three])
  have hs2 : 2 * Real.sqrt a ≤ ss a := by
    nlinarith [ss_mul_self ha, Real.mul_self_sqrt ha.le, Real.sqrt_nonneg a, ss_pos ha]
  have h3 : 2 / ss a ≤ (Real.sqrt a)⁻¹ := by
    rw [div_le_iff₀ (ss_pos ha)]
    calc (2 : ℝ) = (Real.sqrt a)⁻¹ * (2 * Real.sqrt a) := by field_simp
      _ ≤ (Real.sqrt a)⁻¹ * ss a := mul_le_mul_of_nonneg_left hs2 (inv_nonneg.2 hr0.le)
  rw [hr]
  exact h3

lemma moment0 {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Pl => |heatKd 0 a z| * Real.cosh z.2) ∧
      (∫ z : Pl, |heatKd 0 a z| * Real.cosh z.2) ≤ Real.exp a * (1 + a ^ (-(1 / 2 : ℝ))) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hs0 : ss a ≠ 0 := (ss_pos ha).ne'
  have hpt : (fun z : Pl => |heatKd 0 a z| * Real.cosh z.2) = fun z : Pl =>
      (1 / (2 * a)) * ((|z.1| * KK a z.1) * (KK a z.2 * Real.cosh z.2)) := by
    funext z
    have h1 : 0 < KK a z.1 := mul_pos (inv_pos.2 (ss_pos ha)) (Real.exp_pos _)
    have h2 : 0 < KK a z.2 := mul_pos (inv_pos.2 (ss_pos ha)) (Real.exp_pos _)
    unfold heatKd
    rw [heatK_eq_prod ha]
    simp only [Matrix.cons_val_zero]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * a),
      abs_of_pos (mul_pos h1 h2)]
    ring
  have hC := integrable_KK_cosh ha
  have hA := integrable_absKK ha
  have hI : Integrable (fun z : Pl => |heatKd 0 a z| * Real.cosh z.2) := by
    rw [hpt]
    exact (prod_int hA hC).1.const_mul _
  refine ⟨hI, ?_⟩
  rw [hpt, integral_const_mul, (prod_int hA hC).2, integral_abs_KK ha, integral_KK_cosh ha]
  rw [show 1 / (2 * a) * (4 * a / ss a * Real.exp a) = Real.exp a * (2 / ss a) by
    field_simp
    try ring]
  exact mul_le_mul_of_nonneg_left (by linarith [two_div_ss_le ha]) (Real.exp_pos a).le

lemma moment1 {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : Pl => |heatKd 1 a z| * Real.cosh z.2) ∧
      (∫ z : Pl, |heatKd 1 a z| * Real.cosh z.2) ≤ Real.exp a * (1 + a ^ (-(1 / 2 : ℝ))) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hs0 : ss a ≠ 0 := (ss_pos ha).ne'
  have hpt : (fun z : Pl => |heatKd 1 a z| * Real.cosh z.2) = fun z : Pl =>
      (1 / (2 * a)) * (KK a z.1 * (|z.2| * (KK a z.2 * Real.cosh z.2))) := by
    funext z
    have h1 : 0 < KK a z.1 := mul_pos (inv_pos.2 (ss_pos ha)) (Real.exp_pos _)
    have h2 : 0 < KK a z.2 := mul_pos (inv_pos.2 (ss_pos ha)) (Real.exp_pos _)
    unfold heatKd
    rw [heatK_eq_prod ha]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * a),
      abs_of_pos (mul_pos h1 h2)]
    ring
  have hK := integrable_KK ha
  have hB := integrable_abs_KK_cosh ha
  have hI : Integrable (fun z : Pl => |heatKd 1 a z| * Real.cosh z.2) := by
    rw [hpt]
    exact (prod_int hK hB).1.const_mul _
  refine ⟨hI, ?_⟩
  rw [hpt, integral_const_mul, (prod_int hK hB).2, integral_KK ha, one_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (integral_abs_KK_cosh_le ha) (by positivity)) ?_
  rw [show 1 / (2 * a) * (Real.exp a * (4 * a / ss a + 2 * a)) =
      Real.exp a * (2 / ss a + 1) by
    field_simp
    try ring]
  exact mul_le_mul_of_nonneg_left (by linarith [two_div_ss_le ha]) (Real.exp_pos a).le

/-- **`T22/1/3`** Gaussian moments of the heat kernel (Stages.lean `HeatKernelMoments`). -/
theorem heatKernelMoments_aux : HeatKernelMoments := by
  intro a ha
  have hK := integrable_KK ha
  have hC := integrable_KK_cosh ha
  have hfun : heatK a = fun z : Pl => KK a z.1 * KK a z.2 := funext (heatK_eq_prod ha)
  have hC2 : (fun z : Pl => heatK a z * Real.cosh z.2) =
      fun z : Pl => KK a z.1 * (KK a z.2 * Real.cosh z.2) := by
    funext z; rw [heatK_eq_prod ha]; ring
  refine ⟨heatK_pos ha, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]; exact (prod_int hK hK).1
  · rw [hfun, (prod_int hK hK).2, integral_KK ha, one_mul]
  · rw [hC2]; exact (prod_int hK hC).1
  · rw [hC2, (prod_int hK hC).2, integral_KK ha, integral_KK_cosh ha, one_mul]
  · intro i
    fin_cases i
    · exact moment0 ha
    · exact moment1 ha

end HM

/-- **`T22/1/3`** The heat kernel moments (`Stages.lean`, `HeatKernelMoments`). -/
theorem heatKernelMoments : UnforcedLeray.Short.IIb.CylPDE.HeatKernelMoments :=
  HM.heatKernelMoments_aux

end UnforcedLeray.Short.IIb.CylPDE
