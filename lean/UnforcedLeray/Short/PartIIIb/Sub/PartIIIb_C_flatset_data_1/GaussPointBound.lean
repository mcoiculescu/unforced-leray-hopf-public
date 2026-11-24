import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Derivative of the radial profile `gaussE a` (product and chain rules). -/
theorem gaussE_hasDerivAt (a r : ℝ) (ha : a ≠ 0) :
    HasDerivAt (gaussE a)
      ((a ^ 2)⁻¹ * ((-(2 * r) / (2 * a)) * Real.exp (-(r ^ 2) / (4 * a))
        + (2 - r ^ 2 / (2 * a)) * (Real.exp (-(r ^ 2) / (4 * a)) * (-(2 * r) / (4 * a))))) r := by
  have hq : HasDerivAt (fun t : ℝ => 2 - t ^ 2 / (2 * a)) (-(2 * r) / (2 * a)) r := by
    have h := ((hasDerivAt_pow 2 r).div_const (2 * a)).const_sub 2
    exact h.congr_deriv (by norm_num <;> ring)
  have he : HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2) / (4 * a)))
      (Real.exp (-(r ^ 2) / (4 * a)) * (-(2 * r) / (4 * a))) r := by
    have h := ((hasDerivAt_pow 2 r).neg.div_const (4 * a)).exp
    exact h.congr_deriv (by norm_num <;> ring)
  have hm := (hq.mul he).const_mul ((a ^ 2)⁻¹)
  have hfun : gaussE a = fun t : ℝ =>
      (a ^ 2)⁻¹ * ((2 - t ^ 2 / (2 * a)) * Real.exp (-(t ^ 2) / (4 * a))) := by
    funext t
    unfold gaussE
    ring
  rw [hfun]
  exact hm

theorem gaussRdE_eq (a r : ℝ) (ha : a ≠ 0) :
    gaussRdE a r = -((a ^ 2)⁻¹ * (r ^ 2 / (2 * a)) * (4 - r ^ 2 / (2 * a))
      * Real.exp (-(r ^ 2) / (4 * a))) := by
  unfold gaussRdE
  rw [(gaussE_hasDerivAt a r ha).deriv]
  field_simp
  ring

theorem abs_two_sub_le (a r : ℝ) (ha : 1 ≤ a) :
    |2 - r ^ 2 / (2 * a)| ≤ 2 + r ^ 2 / 2 := by
  have hq0 : 0 ≤ r ^ 2 / (2 * a) := div_nonneg (sq_nonneg r) (by linarith)
  have hq1 : r ^ 2 / (2 * a) ≤ r ^ 2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg r) (by norm_num) (by linarith)
  have hr := sq_nonneg r
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem gaussE_abs_le (a r : ℝ) (ha : 1 ≤ a) :
    |gaussE a r| ≤ (2 + r ^ 2 / 2) * Real.exp (-(r ^ 2) / (4 * a)) := by
  unfold gaussE
  have hu0 : 0 ≤ (a ^ 2)⁻¹ := by positivity
  have hu1 : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hE : 0 ≤ Real.exp (-(r ^ 2) / (4 * a)) := (Real.exp_pos _).le
  have hb := abs_two_sub_le a r ha
  rw [abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hE]
  have s1 : (a ^ 2)⁻¹ * |2 - r ^ 2 / (2 * a)| ≤ 1 * (2 + r ^ 2 / 2) :=
    mul_le_mul hu1 hb (abs_nonneg _) zero_le_one
  have s2 := mul_le_mul_of_nonneg_right s1 hE
  linarith

theorem gaussRdE_abs_le (a r : ℝ) (ha : 1 ≤ a) :
    |gaussRdE a r| ≤ (r ^ 2 / 2) * (4 + r ^ 2 / 2) * Real.exp (-(r ^ 2) / (4 * a)) := by
  have ha0 : a ≠ 0 := (by linarith : (0 : ℝ) < a).ne'
  rw [gaussRdE_eq a r ha0, abs_neg]
  have hu0 : 0 ≤ (a ^ 2)⁻¹ := by positivity
  have hu1 : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hq0 : 0 ≤ r ^ 2 / (2 * a) := div_nonneg (sq_nonneg r) (by linarith)
  have hq1 : r ^ 2 / (2 * a) ≤ r ^ 2 / 2 :=
    div_le_div_of_nonneg_left (sq_nonneg r) (by norm_num) (by linarith)
  have hr := sq_nonneg r
  have h4 : |4 - r ^ 2 / (2 * a)| ≤ 4 + r ^ 2 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hE : 0 ≤ Real.exp (-(r ^ 2) / (4 * a)) := (Real.exp_pos _).le
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hu0, abs_of_nonneg hq0, abs_of_nonneg hE]
  have s1 : (a ^ 2)⁻¹ * (r ^ 2 / (2 * a)) ≤ 1 * (r ^ 2 / 2) :=
    mul_le_mul hu1 hq1 hq0 zero_le_one
  have s2 : (a ^ 2)⁻¹ * (r ^ 2 / (2 * a)) * |4 - r ^ 2 / (2 * a)| ≤
      1 * (r ^ 2 / 2) * (4 + r ^ 2 / 2) :=
    mul_le_mul s1 h4 (abs_nonneg _) (by positivity)
  have s3 := mul_le_mul_of_nonneg_right s2 hE
  linarith

theorem angTwo_norm_le (x : ℝ × ℝ) : ‖IIIa.angTwo x‖ ≤ 1 := by
  unfold IIIa.angTwo
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hz : ‖(x.1 : ℂ) + (x.2 : ℂ) * Complex.I‖ ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  rw [hz, abs_of_nonneg (by positivity)]
  exact div_le_one_of_le₀ le_rfl (by positivity)

/-- **Gaussian pointwise bound of the source profiles** (source 4565-4570). -/
theorem gaussPointBound : GaussPointBound := by
  intro A hA
  refine ⟨4, fun a ha x => ?_⟩
  obtain ⟨ha1, haA⟩ := ha
  have hpnn : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := by positivity
  have hq : 1 + x.1 ^ 2 + x.2 ^ 2 = 1 + (x.1 ^ 2 + x.2 ^ 2) := by ring
  have hr2 : planeR x ^ 2 = x.1 ^ 2 + x.2 ^ 2 := by
    unfold planeR
    exact Real.sq_sqrt hpnn
  have hE : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a)) ≤
      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
    apply Real.exp_le_exp.mpr
    have h : (x.1 ^ 2 + x.2 ^ 2) / (4 * A) ≤ (x.1 ^ 2 + x.2 ^ 2) / (4 * a) :=
      div_le_div_of_nonneg_left hpnn (by linarith) (by linarith)
    rw [neg_div, neg_div]
    linarith
  have h1 := gaussRdE_abs_le a (planeR x) ha1
  have h2 := gaussE_abs_le a (planeR x) ha1
  rw [hr2] at h1 h2
  have hA2 := angTwo_norm_le x
  have hEpos : 0 ≤ Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a)) := (Real.exp_pos _).le
  have hEA : 0 ≤ Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := (Real.exp_pos _).le
  have hcoef1 : (x.1 ^ 2 + x.2 ^ 2) / 2 * (4 + (x.1 ^ 2 + x.2 ^ 2) / 2) ≤
      4 * (1 + (x.1 ^ 2 + x.2 ^ 2)) ^ 2 := by
    nlinarith [hpnn]
  have hcoef2 : (x.1 ^ 2 + x.2 ^ 2) / 2 * (4 + (x.1 ^ 2 + x.2 ^ 2) / 2)
      + 2 * (2 + (x.1 ^ 2 + x.2 ^ 2) / 2) ≤ 4 * (1 + (x.1 ^ 2 + x.2 ^ 2)) ^ 2 := by
    nlinarith [hpnn]
  have hc1 : (x.1 ^ 2 + x.2 ^ 2) / 2 * (4 + (x.1 ^ 2 + x.2 ^ 2) / 2) *
      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a)) ≤
      4 * (1 + (x.1 ^ 2 + x.2 ^ 2)) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
    calc _ ≤ (x.1 ^ 2 + x.2 ^ 2) / 2 * (4 + (x.1 ^ 2 + x.2 ^ 2) / 2) *
          Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef1 hEA
  have hc2 : ((x.1 ^ 2 + x.2 ^ 2) / 2 * (4 + (x.1 ^ 2 + x.2 ^ 2) / 2)
      + 2 * (2 + (x.1 ^ 2 + x.2 ^ 2) / 2)) *
      Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a)) ≤
      4 * (1 + (x.1 ^ 2 + x.2 ^ 2)) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) := by
    calc _ ≤ ((x.1 ^ 2 + x.2 ^ 2) / 2 * (4 + (x.1 ^ 2 + x.2 ^ 2) / 2)
          + 2 * (2 + (x.1 ^ 2 + x.2 ^ 2) / 2)) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * A)) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef2 hEA
  constructor
  · rw [hq]
    have hM : ‖hMode a x‖ ≤ |gaussRdE a (planeR x)| := by
      unfold hMode
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) hA2
    calc ‖hMode a x‖ ≤ _ := hM
      _ ≤ _ := h1
      _ ≤ _ := hc1
      _ = _ := by ring
  · rw [hq]
    have hR : ‖rMode a x‖ ≤ |gaussRdE a (planeR x) + 2 * gaussE a (planeR x)| := by
      unfold rMode
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hsplit : |gaussRdE a (planeR x) + 2 * gaussE a (planeR x)| ≤
        |gaussRdE a (planeR x)| + 2 * |gaussE a (planeR x)| := by
      calc _ ≤ |gaussRdE a (planeR x)| + |2 * gaussE a (planeR x)| := abs_add_le _ _
        _ = _ := by rw [abs_mul]; norm_num
    have hlin : |gaussRdE a (planeR x)| + 2 * |gaussE a (planeR x)| ≤
        ((x.1 ^ 2 + x.2 ^ 2) / 2 * (4 + (x.1 ^ 2 + x.2 ^ 2) / 2)
          + 2 * (2 + (x.1 ^ 2 + x.2 ^ 2) / 2)) *
        Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a)) := by
      nlinarith [h1, h2]
    calc ‖rMode a x‖ ≤ _ := hR
      _ ≤ _ := hsplit
      _ ≤ _ := hlin
      _ ≤ _ := hc2
      _ = _ := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
