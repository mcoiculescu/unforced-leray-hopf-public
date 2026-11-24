import UnforcedLeray.Lib.Cylinder.IBP
import Mathlib.Analysis.Fourier.AddCircle

/-!
# `q`-averages and `q`-modes on the cylinder (INF13, target CY04, first part)


§4 BP2 and §5 CY04 (`qAvg`, `qMode`, `qMode_weakPartialQ`).

For a `c`-periodic `f` on the plane (decision D1) and a height `η`, `qMode c hc n f η` is the
`n`-th Fourier coefficient of the slice `q ↦ f (q, η)` on the centred period
`[-c/2, c/2]`, that is `c⁻¹ ∫_{-c/2}^{c/2} e^{-2πinq/c} f(q, η) dq`; `qAvg c f η` is the
`q`-average (the mean mode, `qMode_zero`).  The mean and oscillatory parts of the manuscript
(`v̄`, `F_⊥`; e.g. `paper/main.tex` lines 2598-2608, unit B0173; lines 9077-9085, unit B0566)
are these modes.

* `qMode_zero`: the zeroth mode is the `q`-average;
* `qMode_partialQ`: `(∂_q f)^(n) = (2πin/c) f^(n)` for a `C¹` periodic `f` (the classical form
  of CY04 `qMode_weakPartialQ`);
* `hasSum_sq_qMode`: Parseval on each slice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real Complex
open scoped ENNReal

namespace UnforcedLeray.Cyl

/-- The `q`-average `c⁻¹ ∫_{-c/2}^{c/2} f(q, η) dq` (CY04). -/
def qAvg (c : ℝ) (f : Plane → ℂ) (η : ℝ) : ℂ := (c⁻¹ : ℂ) * ∫ q in Ico (-c / 2) (c / 2), f (q, η)

theorem neg_half_lt_half {c : ℝ} (hc : 0 < c) : -c / 2 < c / 2 := by linarith

/-- The `n`-th `q`-mode of `f` at height `η` (CY04). -/
def qMode (c : ℝ) (hc : 0 < c) (n : ℤ) (f : Plane → ℂ) (η : ℝ) : ℂ :=
  fourierCoeffOn (neg_half_lt_half hc) (fun q => f (q, η)) n

theorem half_sub_neg_half (c : ℝ) : c / 2 - -c / 2 = c := by ring

theorem qMode_eq_integral {c : ℝ} (hc : 0 < c) (n : ℤ) (f : Plane → ℂ) (η : ℝ) :
    qMode c hc n f η = (1 / (c / 2 - -c / 2)) •
      ∫ q in (-c / 2)..(c / 2), fourier (-n) (q : AddCircle (c / 2 - -c / 2)) • f (q, η) :=
  fourierCoeffOn_eq_integral _ n _

/-- The zeroth `q`-mode is the `q`-average. -/
theorem qMode_zero {c : ℝ} (hc : 0 < c) (f : Plane → ℂ) (η : ℝ) :
    qMode c hc 0 f η = qAvg c f η := by
  rw [qMode_eq_integral, qAvg]
  simp only [neg_zero, fourier_zero, one_smul]
  rw [intervalIntegral.integral_of_le (neg_half_lt_half hc).le, integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo, half_sub_neg_half, Complex.real_smul]
  push_cast
  ring

/-- **`q`-modes of a `q`-derivative** (CY04 `qMode_weakPartialQ`, classical form):
for a `C¹`, `c`-periodic `f` and `n ≠ 0`, `(∂_q f)^(n) = (2πin/c) f^(n)`. -/
theorem qMode_partialQ {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (hf : ContDiff ℝ 1 f)
    (hper : IsPeriodic c f) {n : ℤ} (hn : n ≠ 0) (η : ℝ) :
    qMode c hc n (partialQ f) η = (2 * π * I * n / c) * qMode c hc n f η := by
  have hd : ∀ q ∈ uIcc (-c / 2) (c / 2),
      HasDerivAt (fun q => f (q, η)) (partialQ f (q, η)) q := fun q _ =>
    hasDerivAt_sliceQ (hf.differentiable one_ne_zero) q η
  have hi : IntervalIntegrable (fun q => partialQ f (q, η)) volume (-c / 2) (c / 2) :=
    ((C1_partial_of_contDiff hf).1.comp (continuous_id.prodMk continuous_const)).intervalIntegrable
      _ _
  have h := fourierCoeffOn_of_hasDerivAt (neg_half_lt_half hc) hn hd hi
  have hbd : f (c / 2, η) - f (-c / 2, η) = 0 := by rw [hper.neg_half, sub_self]
  simp only [qMode]
  have hcc : ((c / 2 : ℝ) : ℂ) - ((-c / 2 : ℝ) : ℂ) = c := by push_cast; ring
  rw [h, hbd, mul_zero, zero_sub, hcc]
  have hk : (2 * π * I * n : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, hn, Complex.I_ne_zero]
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  field_simp

/-- **Parseval on a slice**: `∑_n |f^(n)(η)|² = c⁻¹ ∫_{-c/2}^{c/2} |f(q, η)|² dq`. -/
theorem hasSum_sq_qMode {c : ℝ} (hc : 0 < c) {f : Plane → ℂ} (η : ℝ)
    (hL2 : MemLp (fun q => f (q, η)) 2 (volume.restrict (Ioc (-c / 2) (c / 2)))) :
    HasSum (fun n : ℤ => ‖qMode c hc n f η‖ ^ 2)
      (c⁻¹ * ∫ q in (-c / 2)..(c / 2), ‖f (q, η)‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn (neg_half_lt_half hc) hL2
  rw [half_sub_neg_half, smul_eq_mul] at h
  exact h

end UnforcedLeray.Cyl
