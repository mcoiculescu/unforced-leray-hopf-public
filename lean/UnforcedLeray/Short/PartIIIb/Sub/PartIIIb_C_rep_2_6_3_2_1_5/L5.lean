import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5

/-!
# `sepMajorantMono` (`PartIII-b:C/rep/2/6/3/2/1/5/5`)

Source `shorter-proof-2026-11-02.tex` 3603-3626, 3800-3807, 4171-4200.
For `l ≥ 0` the base `1 + l‖z‖` is at least `1`, and the exponent `-(4+n)` is at most `-(4+0)`,
so `(1 + l‖z‖)^{-(4+n)} ≤ (1 + l‖z‖)^{-4}`; the other factors are common and nonnegative.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepMajorantMono : SepMajorantMono := by
  intro μ T τ n p hp
  unfold sepMajorant
  have hb : (1 : ℝ) ≤ 1 + p.1 * ‖p.2‖ := by
    have := mul_nonneg hp (norm_nonneg p.2)
    linarith
  have hexp : -(4 + (n : ℝ)) ≤ -(4 + ((0 : ℕ) : ℝ)) := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Nat.cast_zero]
    linarith
  have hpow : (1 + p.1 * ‖p.2‖) ^ (-(4 + (n : ℝ))) ≤
      (1 + p.1 * ‖p.2‖) ^ (-(4 + ((0 : ℕ) : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le hb hexp
  have hp0 : 0 ≤ p.1 ^ (2 * μ.re + 2) := Real.rpow_nonneg hp _
  have hT : 0 ≤ IIIa.tensorNorm (T (τ + 2 * Real.log p.1) p.2) := Real.sqrt_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hp0) hT

end UnforcedLeray.Short.PartIIIb.Concrete
