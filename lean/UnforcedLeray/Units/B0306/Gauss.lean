import UnforcedLeray.Units.B0306.Conv
import UnforcedLeray.Analysis.Heat.Averaging
import UnforcedLeray.Lib.Kernels.GaussDeriv
import UnforcedLeray.Lib.Gaussian.Absorb

/-!
# B0306 helper: the Gaussian facts used in the heat smoothing estimate

Helper module of blueprint unit B0306 (`background:eq:2.48`, `paper/main.tex` lines
5909--5921, infrastructure INF29). The heat kernel `K_ν = UnforcedLeray.Heat.kernel ν`
(the compiled kernel `(4πν)^{-3/2} e^{-|x|²/(4ν)}` of `e^{νΔ}`) has:

* derivatives of every order bounded on all of space (`kernel_bddDerivs`, from the compiled
  Gaussian majorant `UnforcedLeray.Kernels.norm_iteratedFDeriv_heatKernel_le`);
* finite moments `∫ |x|^m K_ν(x) dx` of every order (`integrable_pow_mul_kernel`);
* vanishing odd moments, in particular the first one used at tex line 5917
  (`integral_kernel_smul_odd`);
* Gaussian decay beating every power (`exp_le_div_pow`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology

namespace UnforcedLeray.B0306

/-- The heat kernel is even. -/
theorem kernel_neg (ν : ℝ) (x : Space) : Heat.kernel ν (-x) = Heat.kernel ν x := by
  simp only [Heat.kernel_formula, norm_neg]

/-- Every derivative of the heat kernel at a positive time is bounded. -/
theorem kernel_bddDerivs {ν : ℝ} (hν : 0 < ν) : BddDerivs (Heat.kernel ν) := by
  intro k
  refine ⟨Kernels.heatDerivConst k * ν ^ (-((3 + k : ℝ) / 2)), fun x => ?_⟩
  refine (Kernels.norm_iteratedFDeriv_heatKernel_le k hν x).trans ?_
  have h1 : Real.exp (-‖x‖ ^ 2 / (8 * ν)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    have : 0 ≤ ‖x‖ ^ 2 / (8 * ν) := by positivity
    linarith
  have h0 : 0 ≤ Kernels.heatDerivConst k * ν ^ (-((3 + k : ℝ) / 2)) :=
    mul_nonneg (Kernels.heatDerivConst_pos k).le (Real.rpow_nonneg hν.le _)
  calc Kernels.heatDerivConst k * ν ^ (-((3 + k : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / (8 * ν))
      ≤ Kernels.heatDerivConst k * ν ^ (-((3 + k : ℝ) / 2)) * 1 :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = Kernels.heatDerivConst k * ν ^ (-((3 + k : ℝ) / 2)) := mul_one _

/-- Gaussian moments of every order are finite: `x ↦ |x|^m K_ν(x)` is integrable. -/
theorem integrable_pow_mul_kernel {ν : ℝ} (hν : 0 < ν) (m : ℕ) :
    Integrable (fun x : Space => ‖x‖ ^ m * Heat.kernel ν x) := by
  have ha : 0 < (4 * ν)⁻¹ / 2 := by positivity
  obtain ⟨C, hC0, hC⟩ := Gaussian.rpow_mul_exp_neg_mul_sq_le (m := (m : ℝ))
    (b := (4 * ν)⁻¹ / 2) (Nat.cast_nonneg m) ha
  have hN : 0 ≤ (4 * Real.pi * ν) ^ (-(3 : ℝ) / 2) := by positivity
  have hint : Integrable (fun x : Space =>
      ((4 * Real.pi * ν) ^ (-(3 : ℝ) / 2) * C) * Real.exp (-((4 * ν)⁻¹ / 2) * ‖x‖ ^ 2)) :=
    (Heat.Gaussian.exp_integrable ha).const_mul _
  refine hint.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact ((continuous_norm.pow m).mul (Kernels.heatKernel_smooth ν).continuous).aestronglyMeasurable
  · have hk : Heat.kernel ν x = (4 * Real.pi * ν) ^ (-(3 : ℝ) / 2) *
        (Real.exp (-((4 * ν)⁻¹ / 2 * ‖x‖ ^ 2)) * Real.exp (-((4 * ν)⁻¹ / 2) * ‖x‖ ^ 2)) := by
      rw [Heat.kernel_formula, ← Real.exp_add]
      congr 2
      ring
    have hb := hC ‖x‖ (norm_nonneg x)
    rw [Real.rpow_natCast] at hb
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg x) m)
      (Heat.kernel_nonneg hν x)), hk]
    calc ‖x‖ ^ m * ((4 * Real.pi * ν) ^ (-(3 : ℝ) / 2) *
          (Real.exp (-((4 * ν)⁻¹ / 2 * ‖x‖ ^ 2)) * Real.exp (-((4 * ν)⁻¹ / 2) * ‖x‖ ^ 2)))
        = (4 * Real.pi * ν) ^ (-(3 : ℝ) / 2) *
            (‖x‖ ^ m * Real.exp (-((4 * ν)⁻¹ / 2 * ‖x‖ ^ 2))) *
            Real.exp (-((4 * ν)⁻¹ / 2) * ‖x‖ ^ 2) := by ring
      _ ≤ (4 * Real.pi * ν) ^ (-(3 : ℝ) / 2) * C * Real.exp (-((4 * ν)⁻¹ / 2) * ‖x‖ ^ 2) := by
        gcongr
      _ = ((4 * Real.pi * ν) ^ (-(3 : ℝ) / 2) * C) * Real.exp (-((4 * ν)⁻¹ / 2) * ‖x‖ ^ 2) := rfl

/-- Odd integrands against the even heat kernel integrate to zero; with `h` linear this is the
vanishing first Gaussian moment of tex line 5917. -/
theorem integral_kernel_smul_odd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : ℝ) (h : Space → E) (hodd : ∀ x, h (-x) = -h x) :
    ∫ x, Heat.kernel ν x • h x = 0 := by
  have h1 := integral_neg_eq_self (fun x => Heat.kernel ν x • h x) (volume : Measure Space)
  simp only [kernel_neg, hodd, smul_neg, integral_neg] at h1
  have h2 : (2 : ℝ) • ∫ x, Heat.kernel ν x • h x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h1]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Gaussian decay beats every power: `e^{-a r²} ≤ D / r^m` for `r > 0`. -/
theorem exp_le_div_pow {a : ℝ} (ha : 0 < a) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : ℝ, 0 < r → Real.exp (-(a * r ^ 2)) ≤ D / r ^ m := by
  obtain ⟨D, hD0, hD⟩ := Gaussian.rpow_mul_exp_neg_mul_sq_le (m := (m : ℝ)) (b := a)
    (Nat.cast_nonneg m) ha
  refine ⟨D, hD0, fun r hr => ?_⟩
  have h := hD r hr.le
  rw [Real.rpow_natCast] at h
  rw [le_div_iff₀ (pow_pos hr m)]
  linarith [mul_comm (r ^ m) (Real.exp (-(a * r ^ 2)))]

end UnforcedLeray.B0306
