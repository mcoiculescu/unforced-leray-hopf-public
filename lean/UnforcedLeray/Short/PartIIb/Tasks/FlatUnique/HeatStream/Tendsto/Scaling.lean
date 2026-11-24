import UnforcedLeray.Units.B0284.Defs
import UnforcedLeray.Units.B0296.Kernel
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Helper for `PartII-b:T11/3/6`: parabolic scaling and an exponential-moment bound of the planar
heat kernel.

Supports `HeatStream/Tendsto.lean`. Scaling: `G_{r²}(r w) = r⁻² G_1(w)`, so that
`∫ G_{r²}(w) g(w) dw = ∫ G_1(u) g(r u) du`. Exponential moment: `G_1(u) e^{|u₂|}` is integrable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb.TendstoAux

theorem heatKernel_scale_sqr' {r : ℝ} (hr : 0 < r) (x : ℝ) :
    UnforcedLeray.B0191.heatKernel 1 (r ^ 2) (r * x) =
      r⁻¹ * UnforcedLeray.B0191.heatKernel 1 1 x := by
  have hroot : Real.sqrt (4 * Real.pi * 1 * r ^ 2) =
      r * Real.sqrt (4 * Real.pi * 1 * 1) := by
    rw [show 4 * Real.pi * 1 * r ^ 2 = (4 * Real.pi * 1 * 1) * r ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hr]
    ring
  have hexp : -(r * x) ^ 2 / (4 * 1 * r ^ 2) = -x ^ 2 / (4 * 1 * 1) := by
    field_simp
  unfold UnforcedLeray.B0191.heatKernel
  rw [hroot, hexp]
  field_simp

theorem heatKernel2_scale_sq {r : ℝ} (hr : 0 < r) (w : ℝ × ℝ) :
    UnforcedLeray.B0284.heatKernel2 (r ^ 2) (r • w) =
      (r ^ 2)⁻¹ * UnforcedLeray.B0284.heatKernel2 1 w := by
  change UnforcedLeray.B0191.heatKernel 1 (r ^ 2) (r * w.1) *
      UnforcedLeray.B0191.heatKernel 1 (r ^ 2) (r * w.2) =
    (r ^ 2)⁻¹ * (UnforcedLeray.B0191.heatKernel 1 1 w.1 * UnforcedLeray.B0191.heatKernel 1 1 w.2)
  rw [heatKernel_scale_sqr' hr, heatKernel_scale_sqr' hr]
  have h2 : (r ^ 2)⁻¹ = r⁻¹ * r⁻¹ := by
    rw [sq, mul_inv]
  rw [h2]
  ring

/-- Parabolic change of variables for the planar Gaussian:
`∫ G_{r²}(w) g(w) dw = ∫ G_1(u) g(r u) du` for `r > 0`. -/
theorem integral_heatKernel2_scale {r : ℝ} (hr : 0 < r) (g : ℝ × ℝ → ℝ) :
    ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (r ^ 2) w * g w =
      ∫ u : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 u * g (r • u) := by
  have hcomp := MeasureTheory.Measure.integral_comp_smul (volume : Measure (ℝ × ℝ))
    (fun w : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 (r ^ 2) w * g w) r
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hdim] at hcomp
  have hL : ∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (r ^ 2) (r • x) * g (r • x)
      = (r ^ 2)⁻¹ * ∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 x * g (r • x) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [heatKernel2_scale_sq hr x]
    ring
  have hR : |(r ^ 2)⁻¹| = (r ^ 2)⁻¹ := abs_of_pos (by positivity)
  have hcomp' := hcomp
  rw [hR, smul_eq_mul] at hcomp'
  have key : (r ^ 2)⁻¹ * ∫ x : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 1 x * g (r • x)
      = (r ^ 2)⁻¹ * ∫ w : ℝ × ℝ, UnforcedLeray.B0284.heatKernel2 (r ^ 2) w * g w := by
    rw [← hL]
    exact hcomp'
  exact (mul_left_cancel₀ (by positivity) key).symm

/-- The unit planar Gaussian weighted by `e^{|u₂|}` is integrable. -/
theorem integrable_heatKernel2_mul_exp_abs :
    Integrable (fun u : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 1 u * Real.exp |u.2|) := by
  have h1 : Integrable (UnforcedLeray.B0191.heatKernel 1 1) :=
    UnforcedLeray.B0296.integrable_heatKernel1 one_pos
  have h2 : Integrable (fun t : ℝ => Real.exp |t| * UnforcedLeray.B0191.heatKernel 1 1 t) := by
    refine Integrable.mono'
      ((integrable_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).const_mul
        ((Real.sqrt (4 * Real.pi))⁻¹ * Real.exp 2)) ?_ ?_
    · have hc : Continuous (fun t : ℝ =>
          Real.exp |t| * UnforcedLeray.B0191.heatKernel 1 1 t) := by
        unfold UnforcedLeray.B0191.heatKernel
        fun_prop
      exact hc.aestronglyMeasurable
    · refine Eventually.of_forall (fun t => ?_)
      have hk : UnforcedLeray.B0191.heatKernel 1 1 t =
          (Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 4) := by
        unfold UnforcedLeray.B0191.heatKernel
        norm_num
      have hnn : 0 ≤ Real.exp |t| * UnforcedLeray.B0191.heatKernel 1 1 t :=
        mul_nonneg (Real.exp_pos _).le
          (UnforcedLeray.B0191.heatKernel_pos one_pos one_pos t).le
      rw [Real.norm_of_nonneg hnn, hk]
      have hexp : Real.exp |t| ≤ Real.exp (t ^ 2 / 8) * Real.exp 2 := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [sq_abs t, abs_nonneg t, sq_nonneg (|t| - 4)]
      have hsplit : Real.exp (-t ^ 2 / 4) * Real.exp (t ^ 2 / 8) =
          Real.exp (-(1 / 8) * t ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hinv : 0 ≤ (Real.sqrt (4 * Real.pi))⁻¹ := by positivity
      have hEp : 0 ≤ Real.exp (-t ^ 2 / 4) := (Real.exp_pos _).le
      calc Real.exp |t| * ((Real.sqrt (4 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 4))
          = (Real.sqrt (4 * Real.pi))⁻¹ * (Real.exp |t| * Real.exp (-t ^ 2 / 4)) := by ring
        _ ≤ (Real.sqrt (4 * Real.pi))⁻¹ *
            ((Real.exp (t ^ 2 / 8) * Real.exp 2) * Real.exp (-t ^ 2 / 4)) := by
          gcongr
        _ = (Real.sqrt (4 * Real.pi))⁻¹ * Real.exp 2 *
            (Real.exp (-t ^ 2 / 4) * Real.exp (t ^ 2 / 8)) := by ring
        _ = (Real.sqrt (4 * Real.pi))⁻¹ * Real.exp 2 * Real.exp (-(1 / 8) * t ^ 2) := by
          rw [hsplit]
  have hEq : (fun u : ℝ × ℝ => UnforcedLeray.B0284.heatKernel2 1 u * Real.exp |u.2|) =
      fun u : ℝ × ℝ => UnforcedLeray.B0191.heatKernel 1 1 u.1 *
        (Real.exp |u.2| * UnforcedLeray.B0191.heatKernel 1 1 u.2) := by
    funext u
    unfold UnforcedLeray.B0284.heatKernel2
    ring
  rw [hEq]
  exact h1.mul_prod h2

end UnforcedLeray.Short.IIb.TendstoAux
