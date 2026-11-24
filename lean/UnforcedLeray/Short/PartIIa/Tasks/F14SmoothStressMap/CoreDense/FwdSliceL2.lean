import UnforcedLeray.Short.PartIIa.Sub.F14_1_org.Defs
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.HeatGaussL2
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.HeatGaussEquation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Part II-a, task `PartII-a:F14/1/1/5`: the slice bound of the remainder

Target: `FwdSliceL2` (defined in `Sub/F14_1_org/Defs.lean`).

Source of record: `the November 2 reference manuscript`, lines 1375-1376 at `r = 2`.

Proof. Unfold `fwdIntegrand` at `t = M`: the slice is `y ↦ c • G (e^{M/2} • y)` with
`c = exp(-((μ - 1/2) M))` and `G z = heatGauss f (fwdW ν M) (τ - M, z)`.
* `‖c‖ = exp(-(Re μ - 1/2) M)` (`Complex.norm_exp`).
* Dilation in dimension `3`: `eLpNorm (G (λ • ·)) 2 = λ^{-3/2} eLpNorm G 2` for `λ = e^{M/2}`,
  i.e. the factor `exp(-3M/4)`; proved by `map_addHaar_smul` and `eLpNorm_map_measure`.
* The heat contraction `HeatGaussL2` at the phase `τ - M`.
The exponents add up: `-(Re μ - 1/2) M - 3M/4 = -(Re μ + 1/4) M`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace

/-- Dilation on `Space = ℝ³` in the `L²` norm: for `r = e^s`,
`‖g(r ·)‖_{L²} = r^{-3/2} ‖g‖_{L²}`. -/
private theorem eLpNorm_dilate_exp (s : ℝ) (g : Space → CVec3) (hg : Continuous g) :
    eLpNorm (fun y : Space => g (Real.exp s • y)) 2 volume =
      ENNReal.ofReal (Real.exp (-(3 / 2 : ℝ) * s)) * eLpNorm g 2 volume := by
  have hr0 : (0 : ℝ) < Real.exp s := Real.exp_pos s
  have hφ : Measurable (fun y : Space => Real.exp s • y) :=
    (continuous_const_smul (Real.exp s)).measurable
  have hmap := MeasureTheory.Measure.map_addHaar_smul (μ := (volume : Measure Space))
    (r := Real.exp s) hr0.ne'
  rw [finrank_euclideanSpace_fin] at hmap
  have h3 : Real.exp s ^ 3 = Real.exp (3 * s) := by
    rw [← Real.exp_nat_mul]; norm_num
  have hc : |((Real.exp s) ^ 3)⁻¹| = Real.exp (-(3 * s)) := by
    rw [h3, abs_of_pos (by positivity), Real.exp_neg]
  have key : eLpNorm (fun y : Space => g (Real.exp s • y)) 2 volume =
      eLpNorm g 2 (Measure.map (fun y : Space => Real.exp s • y) volume) :=
    (eLpNorm_map_measure hg.aestronglyMeasurable hφ.aemeasurable).symm
  rw [key, hmap, eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), hc]
  have hexp : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [hexp, smul_eq_mul, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
    ← Real.exp_mul]
  congr 2
  ring_nf

/-- **The slice bound of the remainder** (line 1375-1376 at `r = 2`, `γ_2 = 1/4`):
`‖e^{-μM}[S(M) f(τ - M)]‖_{L²} ≤ e^{-(Re μ + 1/4)M} ‖f(τ - M)‖_{L²}`. -/
theorem fwdSliceL2 : FwdSliceL2 := by
  intro P ν hP hν μ f hf M τ hM
  have hcd : ContDiff ℝ ∞ (heatGauss f (fwdW ν M)) :=
    UnforcedLeray.Short.PartIIa.HeatGaussEquationAux.heatGauss_contDiff hP hf (fwdW ν M)
  have hG : Continuous (fun z : Space => heatGauss f (fwdW ν M) (τ - M, z)) :=
    hcd.continuous.comp (continuous_const.prodMk continuous_id)
  have hfun : (fun y : Space => fwdIntegrand ν μ f M (τ, y)) =
      Complex.exp (-((μ - 1 / 2) * (M : ℂ))) •
        (fun y : Space => heatGauss f (fwdW ν M) (τ - M, Real.exp (M / 2) • y)) := by
    funext y
    rfl
  have hnorm : ‖Complex.exp (-((μ - 1 / 2) * (M : ℂ)))‖ =
      Real.exp (-((μ.re - 1 / 2) * M)) := by
    rw [Complex.norm_exp]
    congr 1
    have h12re : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    have h12im : ((1 / 2 : ℂ)).im = 0 := by norm_num
    simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, h12re, h12im]
    ring_nf
  have hH := UnforcedLeray.Short.PartIIa.heatGaussL2 P hP f hf (fwdW ν M) (τ - M)
  rw [hfun, eLpNorm_const_smul, eLpNorm_dilate_exp (M / 2) (fun z : Space => heatGauss f (fwdW ν M) (τ - M, z)) hG]
  rw [← ofReal_norm, hnorm]
  calc ENNReal.ofReal (Real.exp (-((μ.re - 1 / 2) * M))) *
        (ENNReal.ofReal (Real.exp (-(3 / 2 : ℝ) * (M / 2))) *
          eLpNorm (fun z : Space => heatGauss f (fwdW ν M) (τ - M, z)) 2 volume)
      ≤ ENNReal.ofReal (Real.exp (-((μ.re - 1 / 2) * M))) *
        (ENNReal.ofReal (Real.exp (-(3 / 2 : ℝ) * (M / 2))) *
          eLpNorm (fun z : Space => f (τ - M, z)) 2 volume) := by
        gcongr
    _ = ENNReal.ofReal (Real.exp (-(μ.re + 1 / 4) * M)) *
          eLpNorm (fun y : Space => f (τ - M, y)) 2 volume := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        ring_nf

end UnforcedLeray.Short.PartIIa
