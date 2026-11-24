import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# B0592 helper: Cauchy–Schwarz and the Schur test for nonnegative kernels

Helper for blueprint unit **B0592** (`prepared:p4.4a`, `paper/main.tex` lines 9594–9608):
"Young's inequality near the diagonal" (line 9596). We use the `L¹ ⋆ L² → L²` case in its
kernel (Schur) form: if `∫ k(x, y) dy ≤ A` for every `x` and `∫ k(x, y) dx ≤ B` for every `y`, then
`∫ (∫ k(x, y) f(y) dy)² dx ≤ A B ∫ f²`. For a translation kernel `k(x, y) = g(x - y)` this is
Young's inequality `‖g ⋆ f‖₂ ≤ ‖g‖₁ ‖f‖₂`. Everything is stated in `ℝ≥0∞`, so no integrability
side conditions (and no junk values) occur.

Proof: pointwise Cauchy–Schwarz `(∫ k f)² ≤ (∫ k)(∫ k f²)` (from
`ENNReal.lintegral_mul_norm_pow_le` with exponents `1/2, 1/2`), then Tonelli.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.B0592

theorem ennreal_sq_rpow_half (a : ℝ≥0∞) : (a ^ 2) ^ (1 / 2 : ℝ) = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem ennreal_rpow_half_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem ennreal_le_of_sq_le_sq {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rwa [ennreal_sq_rpow_half, ennreal_sq_rpow_half] at this

/-- Cauchy–Schwarz for lower Lebesgue integrals. -/
theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_norm_pow_le (μ := μ) (hf.pow_const 2) (hg.pow_const 2)
    (p := 1 / 2) (q := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  simp only [ennreal_sq_rpow_half] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, ennreal_rpow_half_sq, ennreal_rpow_half_sq]

/-- **Schur test** (the kernel form of Young's `L¹ ⋆ L² → L²` inequality). -/
theorem schur_test {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {k : α → β → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) {f : β → ℝ≥0∞} (hf : Measurable f) {A B : ℝ≥0∞}
    (hA : ∀ x, ∫⁻ y, k x y ∂ν ≤ A) (hB : ∀ y, ∫⁻ x, k x y ∂μ ≤ B) :
    ∫⁻ x, (∫⁻ y, k x y * f y ∂ν) ^ 2 ∂μ ≤ A * B * ∫⁻ y, f y ^ 2 ∂ν := by
  have hkx : ∀ x, Measurable (k x) := fun x => hk.of_uncurry_left
  have hky : ∀ y, Measurable fun x => k x y := fun y => hk.of_uncurry_right
  have hpt : ∀ x, (∫⁻ y, k x y * f y ∂ν) ^ 2 ≤ A * ∫⁻ y, k x y * f y ^ 2 ∂ν := by
    intro x
    have hsq : ∀ y, k x y * f y = k x y ^ (1 / 2 : ℝ) * (k x y ^ (1 / 2 : ℝ) * f y) := by
      intro y
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← sq,
        ennreal_sq_rpow_half]
    have hcs := lintegral_mul_sq_le (μ := ν) (f := fun y => k x y ^ (1 / 2 : ℝ))
      (g := fun y => k x y ^ (1 / 2 : ℝ) * f y) ((hkx x).pow_const _).aemeasurable
      (((hkx x).pow_const _).mul hf).aemeasurable
    simp only [mul_pow, ennreal_rpow_half_sq] at hcs
    rw [lintegral_congr hsq]
    calc _ ≤ (∫⁻ y, k x y ∂ν) * ∫⁻ y, k x y * f y ^ 2 ∂ν := hcs
      _ ≤ A * ∫⁻ y, k x y * f y ^ 2 ∂ν := mul_le_mul_left (hA x) _
  have hjoint : Measurable fun p : α × β => k p.1 p.2 * f p.2 ^ 2 :=
    hk.mul ((hf.comp measurable_snd).pow_const 2)
  calc ∫⁻ x, (∫⁻ y, k x y * f y ∂ν) ^ 2 ∂μ
      ≤ ∫⁻ x, A * ∫⁻ y, k x y * f y ^ 2 ∂ν ∂μ := lintegral_mono hpt
    _ = A * ∫⁻ x, ∫⁻ y, k x y * f y ^ 2 ∂ν ∂μ :=
        lintegral_const_mul _ hjoint.lintegral_prod_right'
    _ = A * ∫⁻ y, ∫⁻ x, k x y * f y ^ 2 ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = A * ∫⁻ y, (∫⁻ x, k x y ∂μ) * f y ^ 2 ∂ν := by
        congr 1
        refine lintegral_congr fun y => ?_
        rw [lintegral_mul_const _ (hky y)]
    _ ≤ A * ∫⁻ y, B * f y ^ 2 ∂ν :=
        mul_le_mul_right (lintegral_mono fun y => mul_le_mul_left (hB y) _) A
    _ = A * B * ∫⁻ y, f y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hf.pow_const 2), mul_assoc]

end UnforcedLeray.B0592
