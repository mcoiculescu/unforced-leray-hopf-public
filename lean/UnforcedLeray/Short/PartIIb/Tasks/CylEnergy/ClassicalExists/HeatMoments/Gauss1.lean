import UnforcedLeray.Short.PartIIb.Sub.T22_1.Stages
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Helper for `PartII-b:T22/1/3`: one-dimensional Gaussian moments

With `b = 1/(4a)` and `s = √(π/b) = √(4πa)`, the normalized Gaussian is `KK a t = s⁻¹ exp(-b t²)`.
This file proves the one-dimensional facts used by `HeatMoments.lean`: mass, the `cosh` moment,
the absolute-value moments and their shifted versions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb.CylPDE.HM

/-- `b = 1/(4a)`. -/
def bb (a : ℝ) : ℝ := 1 / (4 * a)

/-- `s = √(π/b) = √(4πa)`. -/
def ss (a : ℝ) : ℝ := Real.sqrt (Real.pi / bb a)

/-- The normalized one-dimensional Gaussian `t ↦ s⁻¹ exp(-b t²)`. -/
def KK (a t : ℝ) : ℝ := (ss a)⁻¹ * Real.exp (-(bb a) * t ^ 2)

lemma bb_pos {a : ℝ} (ha : 0 < a) : 0 < bb a := by
  unfold bb; positivity

lemma ss_pos {a : ℝ} (ha : 0 < a) : 0 < ss a := by
  unfold ss
  apply Real.sqrt_pos.2
  have := bb_pos ha
  positivity

lemma ss_mul_self {a : ℝ} (ha : 0 < a) : ss a * ss a = 4 * Real.pi * a := by
  unfold ss bb
  rw [Real.mul_self_sqrt (by have := Real.pi_pos; positivity)]
  field_simp

lemma bb_mul_four {a : ℝ} (ha : 0 < a) : bb a * (4 * a) = 1 := by
  unfold bb
  field_simp

lemma heatK_eq_prod {a : ℝ} (ha : 0 < a) (z : Pl) :
    heatK a z = KK a z.1 * KK a z.2 := by
  have hs := ss_mul_self ha
  have hinv : 1 / (4 * Real.pi * a) = (ss a)⁻¹ * (ss a)⁻¹ := by
    rw [← mul_inv, hs, one_div]
  have hexp : -(z.1 ^ 2 + z.2 ^ 2) / (4 * a) = -(bb a) * z.1 ^ 2 + -(bb a) * z.2 ^ 2 := by
    unfold bb; ring
  unfold heatK KK
  rw [hinv, hexp, Real.exp_add]
  ring

lemma integrable_KK {a : ℝ} (ha : 0 < a) : Integrable (KK a) := by
  unfold KK
  exact (integrable_exp_neg_mul_sq (bb_pos ha)).const_mul _

lemma integral_KK {a : ℝ} (ha : 0 < a) : ∫ t, KK a t = 1 := by
  unfold KK
  rw [integral_const_mul, integral_gaussian]
  unfold ss
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (by have := bb_pos ha; positivity)).ne'

lemma gauss_shift_minus {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Real.exp (-(bb a) * (t - 2 * a) ^ 2) =
      Real.exp (-(bb a) * t ^ 2) * Real.exp t * Real.exp (-a) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination (t - a) * bb_mul_four ha

lemma gauss_shift_plus {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Real.exp (-(bb a) * (t + 2 * a) ^ 2) =
      Real.exp (-(bb a) * t ^ 2) * Real.exp (-t) * Real.exp (-a) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  linear_combination (-t - a) * bb_mul_four ha

/-- `K_a(t) cosh t` as a sum of two translated Gaussians. -/
lemma KK_cosh_eq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    KK a t * Real.cosh t =
      (Real.exp a / (2 * ss a)) *
        (Real.exp (-(bb a) * (t - 2 * a) ^ 2) + Real.exp (-(bb a) * (t + 2 * a) ^ 2)) := by
  have hs0 : ss a ≠ 0 := (ss_pos ha).ne'
  rw [gauss_shift_minus ha, gauss_shift_plus ha, Real.cosh_eq, Real.exp_neg t, Real.exp_neg a]
  unfold KK
  field_simp
  try ring

lemma integrable_gsub {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-(bb a) * (t - c) ^ 2)) :=
  (integrable_exp_neg_mul_sq (bb_pos ha)).comp_sub_right c

lemma integrable_gadd {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-(bb a) * (t + c) ^ 2)) :=
  (integrable_exp_neg_mul_sq (bb_pos ha)).comp_add_right c

lemma integral_gsub {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ t : ℝ, Real.exp (-(bb a) * (t - c) ^ 2) = ss a :=
  (integral_sub_right_eq_self (fun u : ℝ => Real.exp (-(bb a) * u ^ 2)) c).trans
    (integral_gaussian _)

lemma integral_gadd {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ t : ℝ, Real.exp (-(bb a) * (t + c) ^ 2) = ss a :=
  (integral_add_right_eq_self (fun u : ℝ => Real.exp (-(bb a) * u ^ 2)) c).trans
    (integral_gaussian _)

lemma integrable_KK_cosh {a : ℝ} (ha : 0 < a) :
    Integrable (fun t => KK a t * Real.cosh t) := by
  have h : (fun t => KK a t * Real.cosh t) = fun t =>
      (Real.exp a / (2 * ss a)) *
        (Real.exp (-(bb a) * (t - 2 * a) ^ 2) + Real.exp (-(bb a) * (t + 2 * a) ^ 2)) :=
    funext (KK_cosh_eq ha)
  rw [h]
  exact ((integrable_gsub ha (2 * a)).add (integrable_gadd ha (2 * a))).const_mul _

lemma integral_KK_cosh {a : ℝ} (ha : 0 < a) : ∫ t, KK a t * Real.cosh t = Real.exp a := by
  have h : (fun t => KK a t * Real.cosh t) = fun t =>
      (Real.exp a / (2 * ss a)) *
        (Real.exp (-(bb a) * (t - 2 * a) ^ 2) + Real.exp (-(bb a) * (t + 2 * a) ^ 2)) :=
    funext (KK_cosh_eq ha)
  have hs0 : ss a ≠ 0 := (ss_pos ha).ne'
  rw [h, integral_const_mul, integral_add (integrable_gsub ha (2 * a))
    (integrable_gadd ha (2 * a)), integral_gsub ha, integral_gadd ha]
  field_simp
  ring

/-- `|t| exp(-b t²)` is integrable. -/
lemma integrable_abs_mul_gauss {a : ℝ} (ha : 0 < a) :
    Integrable (fun u : ℝ => |u| * Real.exp (-(bb a) * u ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (bb_pos ha) (s := 1) (by norm_num)
  have h2 : Integrable (fun x : ℝ => x * Real.exp (-(bb a) * x ^ 2)) := by
    simpa only [Real.rpow_one] using h
  exact h2.abs.congr (Filter.Eventually.of_forall fun u => by simp [abs_mul, Real.abs_exp])

/-- `|u + c| exp(-b u²)` is integrable for every `c`. -/
lemma integrable_abs_shift {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Integrable (fun u : ℝ => |u + c| * Real.exp (-(bb a) * u ^ 2)) := by
  have h1 := integrable_abs_mul_gauss ha
  have h2 : Integrable (fun u : ℝ => |c| * Real.exp (-(bb a) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (bb_pos ha)).const_mul _
  refine Integrable.mono' (h1.add h2) ?_ ?_
  · exact (by fun_prop : Continuous fun u : ℝ => |u + c| * Real.exp (-(bb a) * u ^ 2)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun u => ?_)
    have hE : 0 ≤ Real.exp (-(bb a) * u ^ 2) := (Real.exp_pos _).le
    have h3 : |u + c| ≤ |u| + |c| := abs_add_le u c
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hE]
    nlinarith [mul_le_mul_of_nonneg_right h3 hE]

/-- The absolute moment `∫ |u| exp(-b u²) du = 4a`. -/
lemma integral_abs_gauss {a : ℝ} (ha : 0 < a) :
    ∫ u : ℝ, |u| * Real.exp (-(bb a) * u ^ 2) = 4 * a := by
  have e : (fun u : ℝ => |u| * Real.exp (-(bb a) * u ^ 2)) =
      fun u : ℝ => (fun y : ℝ => y * Real.exp (-(bb a) * y ^ 2)) |u| := by
    funext u; simp [sq_abs]
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := bb a)
    (by norm_num) (by norm_num) (bb_pos ha)
  have h' := h
  simp only [Real.rpow_one, Real.rpow_two] at h'
  have hval : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(bb a) * x ^ 2) = 2 * a := by
    rw [h', show ((1:ℝ) + 1) / 2 = 1 by norm_num, Real.Gamma_one,
      show -((1:ℝ) + 1) / 2 = -1 by norm_num, Real.rpow_neg_one]
    unfold bb
    field_simp
    try ring
  rw [e]
  refine (integral_comp_abs (f := fun y : ℝ => y * Real.exp (-(bb a) * y ^ 2))).trans ?_
  show 2 * ∫ x in Ioi (0 : ℝ), x * Real.exp (-(bb a) * x ^ 2) = 4 * a
  rw [hval]
  ring

/-- Translated absolute moment: `∫ |t| exp(-b (t - c)²) dt ≤ 4a + 2a s` for `|c| ≤ 2a`. -/
lemma integral_abs_shift_sub {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 2 * a) :
    ∫ t : ℝ, |t| * Real.exp (-(bb a) * (t - c) ^ 2) ≤ 4 * a + 2 * a * ss a := by
  have e : (fun t : ℝ => |t| * Real.exp (-(bb a) * (t - c) ^ 2)) =
      fun t : ℝ => (fun u : ℝ => |u + c| * Real.exp (-(bb a) * u ^ 2)) (t - c) := by
    funext t; simp
  rw [e, integral_sub_right_eq_self (fun u : ℝ => |u + c| * Real.exp (-(bb a) * u ^ 2)) c]
  have hmono : ∫ u : ℝ, |u + c| * Real.exp (-(bb a) * u ^ 2) ≤
      ∫ u : ℝ, (|u| * Real.exp (-(bb a) * u ^ 2) + (2 * a) * Real.exp (-(bb a) * u ^ 2)) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun u => by positivity)
    · exact (integrable_abs_mul_gauss ha).add
        ((integrable_exp_neg_mul_sq (bb_pos ha)).const_mul _)
    · refine Filter.Eventually.of_forall (fun u => ?_)
      have hE : 0 ≤ Real.exp (-(bb a) * u ^ 2) := (Real.exp_pos _).le
      have h1 : |u + c| ≤ |u| + 2 * a := by
        have := abs_add_le u c
        linarith
      nlinarith [mul_le_mul_of_nonneg_right h1 hE]
  have hval : ∫ u : ℝ, (|u| * Real.exp (-(bb a) * u ^ 2) + (2 * a) * Real.exp (-(bb a) * u ^ 2)) =
      4 * a + 2 * a * ss a := by
    have hg : ∫ u : ℝ, Real.exp (-(bb a) * u ^ 2) = ss a := integral_gaussian (bb a)
    rw [integral_add (integrable_abs_mul_gauss ha)
      ((integrable_exp_neg_mul_sq (bb_pos ha)).const_mul _), integral_const_mul,
      integral_abs_gauss ha, hg]
  linarith [hmono, hval]

/-- Translated absolute moment, plus-form: `∫ |t| exp(-b (t + c)²) dt ≤ 4a + 2a s` for `|c| ≤ 2a`. -/
lemma integral_abs_shift_add {a : ℝ} (ha : 0 < a) (c : ℝ) (hc : |c| ≤ 2 * a) :
    ∫ t : ℝ, |t| * Real.exp (-(bb a) * (t + c) ^ 2) ≤ 4 * a + 2 * a * ss a := by
  have e : (fun t : ℝ => |t| * Real.exp (-(bb a) * (t + c) ^ 2)) =
      fun t : ℝ => (fun u : ℝ => |u - c| * Real.exp (-(bb a) * u ^ 2)) (t + c) := by
    funext t; simp
  rw [e, integral_add_right_eq_self (fun u : ℝ => |u - c| * Real.exp (-(bb a) * u ^ 2)) c]
  have hmono : ∫ u : ℝ, |u - c| * Real.exp (-(bb a) * u ^ 2) ≤
      ∫ u : ℝ, (|u| * Real.exp (-(bb a) * u ^ 2) + (2 * a) * Real.exp (-(bb a) * u ^ 2)) := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun u => by positivity)
    · exact (integrable_abs_mul_gauss ha).add
        ((integrable_exp_neg_mul_sq (bb_pos ha)).const_mul _)
    · refine Filter.Eventually.of_forall (fun u => ?_)
      have hE : 0 ≤ Real.exp (-(bb a) * u ^ 2) := (Real.exp_pos _).le
      have h1 : |u - c| ≤ |u| + 2 * a := by
        have h := abs_add_le u (-c)
        rw [abs_neg, ← sub_eq_add_neg] at h
        linarith
      nlinarith [mul_le_mul_of_nonneg_right h1 hE]
  have hval : ∫ u : ℝ, (|u| * Real.exp (-(bb a) * u ^ 2) + (2 * a) * Real.exp (-(bb a) * u ^ 2)) =
      4 * a + 2 * a * ss a := by
    have hg : ∫ u : ℝ, Real.exp (-(bb a) * u ^ 2) = ss a := integral_gaussian (bb a)
    rw [integral_add (integrable_abs_mul_gauss ha)
      ((integrable_exp_neg_mul_sq (bb_pos ha)).const_mul _), integral_const_mul,
      integral_abs_gauss ha, hg]
  linarith [hmono, hval]

/-- `∫ |t| K_a(t) dt = 4a / s`. -/
lemma integral_abs_KK {a : ℝ} (ha : 0 < a) : ∫ t : ℝ, |t| * KK a t = 4 * a / ss a := by
  have e : (fun t : ℝ => |t| * KK a t) = fun t : ℝ => (ss a)⁻¹ * (|t| * Real.exp (-(bb a) * t ^ 2)) := by
    funext t; unfold KK; ring
  rw [e, integral_const_mul, integral_abs_gauss ha]
  ring

/-- `|t| K_a(t) cosh t` as a sum of two translated absolute Gaussians. -/
lemma abs_KK_cosh_eq {a : ℝ} (ha : 0 < a) :
    (fun t : ℝ => |t| * (KK a t * Real.cosh t)) = fun t : ℝ =>
      (Real.exp a / (2 * ss a)) *
        (|t| * Real.exp (-(bb a) * (t - 2 * a) ^ 2) + |t| * Real.exp (-(bb a) * (t + 2 * a) ^ 2)) := by
  funext t
  rw [KK_cosh_eq ha t]
  ring

lemma integrable_abs_KK_cosh {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => |t| * (KK a t * Real.cosh t)) := by
  rw [abs_KK_cosh_eq ha]
  have i1 : Integrable (fun t : ℝ => |t| * Real.exp (-(bb a) * (t - 2 * a) ^ 2)) := by
    simpa using (integrable_abs_shift ha (2 * a)).comp_sub_right (2 * a)
  have i2 : Integrable (fun t : ℝ => |t| * Real.exp (-(bb a) * (t + 2 * a) ^ 2)) := by
    simpa using (integrable_abs_shift ha (-(2 * a))).comp_add_right (2 * a)
  exact (i1.add i2).const_mul _

lemma integral_abs_KK_cosh_le {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ, |t| * (KK a t * Real.cosh t) ≤ Real.exp a * (4 * a / ss a + 2 * a) := by
  have hs0 : ss a ≠ 0 := (ss_pos ha).ne'
  have hc : |2 * a| ≤ 2 * a := le_of_eq (abs_of_pos (by positivity))
  have hc' : |-(2 * a)| ≤ 2 * a := le_of_eq (by rw [abs_neg, abs_of_pos (by positivity)])
  have hX := integral_abs_shift_sub ha (2 * a) hc
  have hY := integral_abs_shift_add ha (2 * a) hc
  rw [abs_KK_cosh_eq ha, integral_const_mul,
    integral_add (by simpa using (integrable_abs_shift ha (2 * a)).comp_sub_right (2 * a))
      (by simpa using (integrable_abs_shift ha (-(2 * a))).comp_add_right (2 * a))]
  have hpos : 0 ≤ Real.exp a / (2 * ss a) :=
    div_nonneg (Real.exp_pos a).le (by have := ss_pos ha; linarith)
  calc Real.exp a / (2 * ss a) *
        ((∫ t : ℝ, |t| * Real.exp (-(bb a) * (t - 2 * a) ^ 2)) +
          (∫ t : ℝ, |t| * Real.exp (-(bb a) * (t + 2 * a) ^ 2)))
      ≤ Real.exp a / (2 * ss a) * (2 * (4 * a + 2 * a * ss a)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = Real.exp a * (4 * a / ss a + 2 * a) := by
        field_simp
        try ring

end UnforcedLeray.Short.IIb.CylPDE.HM
