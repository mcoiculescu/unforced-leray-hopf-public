import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs

/-!


Source of record `the November 2 reference manuscript` lines 1713-1716.
The trivial bound `‖g^(n)‖ ≤ sup ‖g‖`: `|e^{-2π i n q / c}| = 1` and the average over `[0, c]`
has weight `1/c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- The character `e^{-2π i n q / c}` has modulus one. -/
theorem cnlExp_norm (c : ℝ) (n : ℤ) (q : ℝ) :
    ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ)))‖ = 1 := by
  have h : -(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))
      = (((-(2 * Real.pi * n * q / c)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- **Task target: the trivial bound on the `q`-Fourier coefficient** (source 1713-1716). -/
theorem coeffNormLe : CoeffNormLe := by
  intro c hc g M _ hM n x
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  unfold nzCoeff
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 hc)]
  have hint : ‖∫ q in (0 : ℝ)..c,
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (q : ℂ) / (c : ℂ))) • g (x.1, q, x.2)‖
      ≤ M * |c - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun q _ => by
      rw [norm_smul, cnlExp_norm, one_mul]
      exact hM _)
  calc _ ≤ 1 / c * (M * |c - 0|) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = M := by
      rw [sub_zero, abs_of_pos hc]
      field_simp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
