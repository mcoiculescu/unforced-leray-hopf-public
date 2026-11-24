import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_3_Comb.S1a

/-!
# `gkerMajShiftLe` (`PartIII-b:C/rep/2/6/3/2/1/5/6`)

Source `shorter-proof-2026-11-02.tex` 3603-3626, 3800-3807, 4171-4200.
With `l = e^{-(t-s)/2}` and `lr = e^{-(t₀-s)/2}` the tensor factor is `T(s,z)` on both sides
(`t + 2 log l = s = t₀ + 2 log lr`), `lr ≤ l ≤ e·lr` (since `t₀ - t ≤ 2`), so
`l · l^{2Re μ+2} ≤ e^{2Re μ+3} · lr · lr^{2Re μ+2}` and `(1+l|z|)^{-4} ≤ (1+lr|z|)^{-4}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gkerMajShiftLe : GkerMajShiftLe := by
  intro μ T s t t₀ z hμ hst htt₀ hgap
  have hA : t + 2 * Real.log (Real.exp (-(t - s) / 2)) = s := by
    rw [Real.log_exp]; ring
  have hB : t₀ + 2 * Real.log (Real.exp (-(t₀ - s) / 2)) = s := by
    rw [Real.log_exp]; ring
  have hlr_le : Real.exp (-(t₀ - s) / 2) ≤ Real.exp (-(t - s) / 2) :=
    Real.exp_le_exp.2 (by linarith)
  have hl_le : Real.exp (-(t - s) / 2) ≤ Real.exp 1 * Real.exp (-(t₀ - s) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  have hlr0 : 0 < Real.exp (-(t₀ - s) / 2) := Real.exp_pos _
  have hl0 : 0 < Real.exp (-(t - s) / 2) := Real.exp_pos _
  have ha : (0 : ℝ) ≤ 2 * μ.re + 2 := by linarith
  have hexp : Real.exp (2 * μ.re + 3) = Real.exp 1 * Real.exp (2 * μ.re + 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpow : Real.exp (-(t - s) / 2) ^ (2 * μ.re + 2) ≤
      (Real.exp 1 * Real.exp (-(t₀ - s) / 2)) ^ (2 * μ.re + 2) :=
    Real.rpow_le_rpow hl0.le hl_le ha
  have hpow' : (Real.exp 1 * Real.exp (-(t₀ - s) / 2)) ^ (2 * μ.re + 2) =
      Real.exp (2 * μ.re + 2) * Real.exp (-(t₀ - s) / 2) ^ (2 * μ.re + 2) := by
    rw [Real.mul_rpow (Real.exp_pos 1).le hlr0.le, Real.exp_one_rpow]
  have hX : Real.exp (-(t - s) / 2) * Real.exp (-(t - s) / 2) ^ (2 * μ.re + 2) ≤
      Real.exp (2 * μ.re + 3) *
        (Real.exp (-(t₀ - s) / 2) * Real.exp (-(t₀ - s) / 2) ^ (2 * μ.re + 2)) := by
    calc Real.exp (-(t - s) / 2) * Real.exp (-(t - s) / 2) ^ (2 * μ.re + 2)
        ≤ (Real.exp 1 * Real.exp (-(t₀ - s) / 2)) *
            ((Real.exp 1 * Real.exp (-(t₀ - s) / 2)) ^ (2 * μ.re + 2)) :=
          mul_le_mul hl_le hpow (by positivity) (by positivity)
      _ = (Real.exp 1 * Real.exp (-(t₀ - s) / 2)) *
            (Real.exp (2 * μ.re + 2) * Real.exp (-(t₀ - s) / 2) ^ (2 * μ.re + 2)) := by
          rw [hpow']
      _ = Real.exp (2 * μ.re + 3) *
            (Real.exp (-(t₀ - s) / 2) * Real.exp (-(t₀ - s) / 2) ^ (2 * μ.re + 2)) := by
          rw [hexp]
          ring
  have hP0 : 0 < 1 + Real.exp (-(t₀ - s) / 2) * ‖z‖ := by
    have := mul_nonneg hlr0.le (norm_nonneg z)
    linarith
  have hPle : (1 + Real.exp (-(t - s) / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) ≤
      (1 + Real.exp (-(t₀ - s) / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) := by
    have hxy : 1 + Real.exp (-(t₀ - s) / 2) * ‖z‖ ≤ 1 + Real.exp (-(t - s) / 2) * ‖z‖ := by
      have := mul_le_mul_of_nonneg_right hlr_le (norm_nonneg z)
      linarith
    have hz : -(4 + ((0 : ℕ) : ℝ)) ≤ 0 := by norm_num
    exact Real.rpow_le_rpow_of_nonpos hP0 hxy hz
  have hP0' : 0 ≤ (1 + Real.exp (-(t - s) / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) := by
    positivity
  simp only [gkerMaj, sepMajorant]
  rw [hA, hB]
  have hX' : (1 / 2 : ℝ) * (Real.exp (-(t - s) / 2) * Real.exp (-(t - s) / 2) ^ (2 * μ.re + 2)) ≤
      (1 / 2 : ℝ) * (Real.exp (2 * μ.re + 3) *
        (Real.exp (-(t₀ - s) / 2) * Real.exp (-(t₀ - s) / 2) ^ (2 * μ.re + 2))) :=
    mul_le_mul_of_nonneg_left hX (by norm_num)
  have hN : 0 ≤ IIIa.tensorNorm (T s z) := Real.sqrt_nonneg _
  calc Real.exp (-(t - s) / 2) / 2 * (Real.exp (-(t - s) / 2) ^ (2 * μ.re + 2) *
        (1 + Real.exp (-(t - s) / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) * IIIa.tensorNorm (T s z))
      = (1 / 2 : ℝ) * (Real.exp (-(t - s) / 2) * Real.exp (-(t - s) / 2) ^ (2 * μ.re + 2)) *
          (1 + Real.exp (-(t - s) / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) * IIIa.tensorNorm (T s z) := by
        ring
    _ ≤ (1 / 2 : ℝ) * (Real.exp (2 * μ.re + 3) *
          (Real.exp (-(t₀ - s) / 2) * Real.exp (-(t₀ - s) / 2) ^ (2 * μ.re + 2))) *
          (1 + Real.exp (-(t₀ - s) / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) *
          IIIa.tensorNorm (T s z) := by
        apply mul_le_mul_of_nonneg_right _ hN
        exact mul_le_mul hX' hPle hP0' (by positivity)
    _ = Real.exp (2 * μ.re + 3) * (Real.exp (-(t₀ - s) / 2) / 2 *
          (Real.exp (-(t₀ - s) / 2) ^ (2 * μ.re + 2) *
            (1 + Real.exp (-(t₀ - s) / 2) * ‖z‖) ^ (-(4 + ((0 : ℕ) : ℝ))) *
            IIIa.tensorNorm (T s z))) := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete
