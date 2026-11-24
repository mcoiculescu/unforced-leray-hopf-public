import UnforcedLeray.Units.B0060
import UnforcedLeray.Units.B0094.GaussSchwartz

/-!
# B0061 helper: the coefficients `∂₁E₀`, `∂₂E₀` are Schwartz functions

Helper for blueprint unit **B0061** (`paper/main.tex:1222`: "`A_E f = (Kf)·∇E₀` is bounded
`H^j_M → H^{j+1}_M`", which is `eq:st18-t00049` (unit B0060, tex 1215–1220) "with `b = ∂E₀`").
B0060 is stated for Schwartz coefficients `b ∈ 𝓢(ℝ², ℂ)`; this file realizes the two components
of the Gaussian-vortex gradient `∇E₀` (B0009's `gradE0`, the library's Cartesian gradient of the
planar vorticity) as Schwartz functions:
`∂_k E₀(y) = (|y|²/4 - 2) e^{-|y|²/4} y_k` (`gradE0_eq`, `paper/main.tex:648`).

* `gauss8 : 𝓢(ℂ, ℝ)`, `y ↦ e^{-|y|²/8}`: the Schwartz Gaussian `gaussS` of

  `ℂ` by `Complex.equivRealProdCLM`;
* `gradS k : 𝓢(ℂ, ℂ)`: `e^{-|y|²/8} · ((|y|²/4 - 2) y_k e^{-|y|²/8})`, the second factor of
  temperate growth; `gradS_zero`, `gradS_one`: `gradS 0 = ∂₁E₀`, `gradS 1 = ∂₂E₀` pointwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped SchwartzMap

namespace UnforcedLeray.B0061

open UnforcedLeray.B0009

/-- The Gaussian `e^{-|y|²/8}` on `ℂ = ℝ²` as a Schwartz function (B0094's `gaussS`). -/
def gauss8 : 𝓢(ℂ, ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ Complex.equivRealProdCLM B0094.gaussS

theorem gauss8_apply (y : ℂ) : gauss8 y = Real.exp (-((y.re ^ 2 + y.im ^ 2) / 8)) := rfl

/-- The coordinates `y₁ = Re y`, `y₂ = Im y` (indices `0, 1`). -/
def coord : Fin 2 → ℂ → ℝ
  | 0, y => y.re
  | 1, y => y.im

theorem hasTemperateGrowth_coord (k : Fin 2) : (coord k).HasTemperateGrowth := by
  match k with
  | 0 => exact Complex.reCLM.hasTemperateGrowth
  | 1 => exact Complex.imCLM.hasTemperateGrowth

/-- The temperate-growth factor `(|y|²/4 - 2) y_k e^{-|y|²/8}`. -/
def gradPoly (k : Fin 2) (y : ℂ) : ℂ := (((‖y‖ ^ 2 / 4 - 2) * coord k y * gauss8 y : ℝ) : ℂ)

theorem hasTemperateGrowth_gradPoly (k : Fin 2) : (gradPoly k).HasTemperateGrowth := by
  have hq : (fun y : ℂ => ‖y‖ ^ 2 / 4 - 2).HasTemperateGrowth := by
    have : (fun y : ℂ => ‖y‖ ^ 2 / 4 - 2) =
        (fun _ : ℂ => (1 / 4 : ℝ)) * (fun y : ℂ => ‖y‖ ^ 2) + fun _ : ℂ => (-2 : ℝ) := by
      funext y
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    rw [this]
    exact ((Function.HasTemperateGrowth.const _).mul (Function.hasTemperateGrowth_norm_sq ℂ)).add
      (Function.HasTemperateGrowth.const _)
  have hr : (fun y : ℂ => (‖y‖ ^ 2 / 4 - 2) * coord k y * gauss8 y).HasTemperateGrowth := by
    have : (fun y : ℂ => (‖y‖ ^ 2 / 4 - 2) * coord k y * gauss8 y) =
        (fun y : ℂ => ‖y‖ ^ 2 / 4 - 2) * coord k * ⇑gauss8 := by
      funext y
      simp only [Pi.mul_apply]
    rw [this]
    exact (hq.mul (hasTemperateGrowth_coord k)).mul gauss8.hasTemperateGrowth
  exact Complex.hasTemperateGrowth_ofReal.comp hr

/-- **`∂_k E₀` as a Schwartz function** (`k = 0, 1` for the manuscript's `∂₁, ∂₂`). -/
def gradS (k : Fin 2) : 𝓢(ℂ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) (hasTemperateGrowth_gradPoly k) gauss8

theorem gradS_apply (k : Fin 2) (y : ℂ) :
    gradS k y = (((‖y‖ ^ 2 / 4 - 2) * coord k y * Real.exp (-(‖y‖ ^ 2 / 4)) : ℝ) : ℂ) := by
  rw [gradS, SchwartzMap.bilinLeftCLM_apply]
  simp only [ContinuousLinearMap.lsmul_apply, gradPoly, Complex.real_smul]
  have hn : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have he : Real.exp (-(‖y‖ ^ 2 / 4)) = gauss8 y * gauss8 y := by
    rw [gauss8_apply, ← Real.exp_add, hn]
    congr 1
    ring
  rw [he]
  push_cast
  ring

/-- `gradS 0 = ∂₁E₀` (B0009's `gradE0`, first component). -/
theorem gradS_zero (y : ℂ) : gradS 0 y = ((gradE0 y).1 : ℂ) := by
  rw [gradS_apply, gradE0_eq]
  simp only [coord, GaussianVortex.radialK, GaussianVortex.radialOmega]
  push_cast
  ring

/-- `gradS 1 = ∂₂E₀` (B0009's `gradE0`, second component). -/
theorem gradS_one (y : ℂ) : gradS 1 y = ((gradE0 y).2 : ℂ) := by
  rw [gradS_apply, gradE0_eq]
  simp only [coord, GaussianVortex.radialK, GaussianVortex.radialOmega]
  push_cast
  ring

/-- `A_E f = (Kf)·∇E₀ = ∑_k ∂_k E₀ (Kf)_k` with the Schwartz coefficients. -/
theorem perturbation_eq_sum (f : ℂ → ℂ) (y : ℂ) :
    perturbation f y = ∑ k : Fin 2, gradS k y * biotSavart f k y := by
  rw [Fin.sum_univ_two, gradS_zero, gradS_one, perturbation]
  ring

end UnforcedLeray.B0061
