import UnforcedLeray.Units.B0094.Planar
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# B0094 helper: the Gaussian-polynomial core functions are Schwartz

Blueprint unit B0094 (`eq:st18-t00068`, `paper/main.tex` lines 1503--1505: "Its selfadjoint
closure has Schwartz core"). Under `U_G f = f / √G` (B0093, `eq:st18-t00067`) the core profiles
`r² p(r²) e^{-r²/4} e^{2iϑ}` of `Basis.lean` become `(√4π) (y₁ + i y₂)² p(|y|²) e^{-|y|²/8}`.
This file shows that these functions are Schwartz functions on `ℝ²`:
* `gaussS`: the Gaussian `e^{-|y|²/8}` as an element of `𝓢(ℝ², ℝ)` (Faà di Bruno bound
  `norm_iteratedFDeriv_comp_le` for `exp ∘ (-|y|²/8)`);
* `coreS p`: `U_G` of the core function, as an element of `𝓢(ℝ², ℂ)`
  (`coe_coreS : ⇑(coreS p) = B0093.conjG (angularTwoField (profFun p))`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial
open scoped SchwartzMap Nat ContDiff

namespace UnforcedLeray.B0094

open UnforcedLeray.B0010 UnforcedLeray.GaussianVortex

/-! ## Temperate growth of polynomial expressions -/

theorem hasTemperateGrowth_fst : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.1) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).hasTemperateGrowth

theorem hasTemperateGrowth_snd : Function.HasTemperateGrowth (fun z : ℝ × ℝ => z.2) :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).hasTemperateGrowth

theorem hasTemperateGrowth_sz : Function.HasTemperateGrowth sz := by
  have h1 := hasTemperateGrowth_fst
  have h2 := hasTemperateGrowth_snd
  have : sz = (fun z : ℝ × ℝ => z.1) ^ 2 + (fun z : ℝ × ℝ => z.2) ^ 2 := by
    funext z
    simp [sz]
  rw [this]
  exact (h1.pow 2).add (h2.pow 2)

/-- The exponent `-|y|²/8`. -/
def gaussExp (z : ℝ × ℝ) : ℝ := -((z.1 ^ 2 + z.2 ^ 2) / 8)

theorem hasTemperateGrowth_gaussExp : Function.HasTemperateGrowth gaussExp := by
  have : gaussExp = (fun _ : ℝ × ℝ => (-(1 / 8 : ℝ))) * sz := by
    funext z
    simp only [gaussExp, sz, Pi.mul_apply]
    ring
  rw [this]
  exact (Function.HasTemperateGrowth.const _).mul hasTemperateGrowth_sz

theorem hasTemperateGrowth_ofReal_comp {f : ℝ × ℝ → ℝ} (hf : f.HasTemperateGrowth) :
    Function.HasTemperateGrowth (fun z => (f z : ℂ)) :=
  Complex.hasTemperateGrowth_ofReal.comp hf

theorem hasTemperateGrowth_wz : Function.HasTemperateGrowth wz := by
  have h1 := hasTemperateGrowth_ofReal_comp hasTemperateGrowth_fst
  have h2 := hasTemperateGrowth_ofReal_comp hasTemperateGrowth_snd
  have : wz = (fun z : ℝ × ℝ => (z.1 : ℂ)) +
      (fun z : ℝ × ℝ => (z.2 : ℂ)) * (fun _ : ℝ × ℝ => Complex.I) := by
    funext z
    simp [wz]
  rw [this]
  exact h1.add (h2.mul (Function.HasTemperateGrowth.const _))

theorem hasTemperateGrowth_eval_sz (p : ℂ[X]) :
    Function.HasTemperateGrowth (fun z : ℝ × ℝ => p.eval ((sz z : ℝ) : ℂ)) := by
  have hs := hasTemperateGrowth_ofReal_comp hasTemperateGrowth_sz
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have : (fun z : ℝ × ℝ => (p + q).eval ((sz z : ℝ) : ℂ)) =
        (fun z : ℝ × ℝ => p.eval ((sz z : ℝ) : ℂ)) + fun z => q.eval ((sz z : ℝ) : ℂ) := by
      funext z
      simp
    rw [this]
    exact hp.add hq
  | monomial n a =>
    have : (fun z : ℝ × ℝ => (monomial n a).eval ((sz z : ℝ) : ℂ)) =
        (fun _ : ℝ × ℝ => a) * (fun z : ℝ × ℝ => ((sz z : ℝ) : ℂ)) ^ n := by
      funext z
      simp
    rw [this]
    exact (Function.HasTemperateGrowth.const _).mul (hs.pow n)

/-! ## The Gaussian `e^{-|y|²/8}` is a Schwartz function -/

theorem norm_iteratedFDeriv_exp (i : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ i Real.exp y‖ = Real.exp y := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos y)]

theorem norm_sq_le_sz (z : ℝ × ℝ) : ‖z‖ ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases max_cases |z.1| |z.2| with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h, sq_abs] <;>
    nlinarith [sq_nonneg z.1, sq_nonneg z.2]

/-- `(1 + t)^M e^{-t²/8}` is bounded on `t ≥ 0`. -/
theorem poly_gauss_bound (M : ℕ) :
    ∃ K : ℝ, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ M * Real.exp (-(t ^ 2 / 8)) ≤ K := by
  refine ⟨16 ^ M * (M ! : ℝ) * Real.exp (1 / 8), fun t ht => ?_⟩
  have h1 : (1 + t) ^ M ≤ 2 ^ M * (1 + t ^ 2) ^ M := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (t - 1)]
  have hx : (0 : ℝ) ≤ (1 + t ^ 2) / 8 := by positivity
  have h2 := Real.pow_div_factorial_le_exp _ hx M
  have hfac : (0 : ℝ) < (M ! : ℝ) := by exact_mod_cast Nat.factorial_pos M
  rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h2
  have h3 : Real.exp ((1 + t ^ 2) / 8) * Real.exp (-(t ^ 2 / 8)) = Real.exp (1 / 8) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h16 : (16 : ℝ) ^ M = 2 ^ M * 8 ^ M := by
    rw [← mul_pow]
    norm_num
  have he : 0 ≤ Real.exp (-(t ^ 2 / 8)) := (Real.exp_pos _).le
  calc (1 + t) ^ M * Real.exp (-(t ^ 2 / 8))
      ≤ 2 ^ M * (Real.exp ((1 + t ^ 2) / 8) * (8 ^ M * M !)) * Real.exp (-(t ^ 2 / 8)) := by
        gcongr
        exact h1.trans (by gcongr)
    _ = 16 ^ M * (M ! : ℝ) * Real.exp (1 / 8) := by
        rw [h16, ← h3]
        ring

/-- The Gaussian `e^{-|y|²/8}` as a Schwartz function on `ℝ²`. -/
def gaussS : 𝓢(ℝ × ℝ, ℝ) where
  toFun z := Real.exp (gaussExp z)
  smooth' := Real.contDiff_exp.comp hasTemperateGrowth_gaussExp.1
  decay' k n := by
    obtain ⟨m, C, hC, hb⟩ := hasTemperateGrowth_gaussExp.norm_iteratedFDeriv_le_uniform n
    obtain ⟨K, hK⟩ := poly_gauss_bound (k + m * n)
    refine ⟨n ! * (1 + C) ^ n * K, fun z => ?_⟩
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    set Dz : ℝ := (1 + C) * (1 + ‖z‖) ^ m with hDz
    have hDz1 : 1 ≤ Dz :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
    have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i gaussExp z‖ ≤ Dz ^ i := by
      intro i hi hin
      calc ‖iteratedFDeriv ℝ i gaussExp z‖ ≤ C * (1 + ‖z‖) ^ m := hb i hin z
        _ ≤ Dz := by
          rw [hDz]
          gcongr
          linarith
        _ ≤ Dz ^ i := le_self_pow₀ hDz1 (by omega)
    have hE : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Real.exp (gaussExp z)‖ ≤ Real.exp (gaussExp z) :=
      fun i _ => (norm_iteratedFDeriv_exp i _).le
    have hcomp := norm_iteratedFDeriv_comp_le (N := ∞) Real.contDiff_exp
      hasTemperateGrowth_gaussExp.1 (by exact_mod_cast le_top) z hE hD
    have hexp : Real.exp (gaussExp z) ≤ Real.exp (-(‖z‖ ^ 2 / 8)) := by
      apply Real.exp_le_exp.2
      have := norm_sq_le_sz z
      unfold gaussExp
      linarith
    have hzk : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k := by
      gcongr
      linarith
    have hK' := hK ‖z‖ hz0
    change ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ gaussExp) z‖ ≤ _
    have hfac : (0 : ℝ) ≤ (n ! : ℝ) := by positivity
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (Real.exp ∘ gaussExp) z‖
        ≤ (1 + ‖z‖) ^ k * (n ! * Real.exp (-(‖z‖ ^ 2 / 8)) * Dz ^ n) := by
          apply mul_le_mul hzk _ (norm_nonneg _) (by positivity)
          exact hcomp.trans (by gcongr)
      _ = n ! * (1 + C) ^ n * ((1 + ‖z‖) ^ (k + m * n) * Real.exp (-(‖z‖ ^ 2 / 8))) := by
          rw [hDz, mul_pow, ← pow_mul, pow_add]
          ring
      _ ≤ n ! * (1 + C) ^ n * K := by gcongr

theorem gaussS_apply (z : ℝ × ℝ) : gaussS z = Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) := rfl

/-! ## The core functions `U_G (r² p(r²) e^{-r²/4} e^{2iϑ})` are Schwartz -/

/-- The polynomial factor `(√4π) (y₁ + i y₂)² p(|y|²)` (`√4π = sqrtConst⁻¹`). -/
def corePoly (p : ℂ[X]) (z : ℝ × ℝ) : ℂ :=
  ((B0093.sqrtConst⁻¹ : ℝ) : ℂ) * (wz z ^ 2 * p.eval ((sz z : ℝ) : ℂ))

theorem hasTemperateGrowth_corePoly (p : ℂ[X]) : Function.HasTemperateGrowth (corePoly p) := by
  have : corePoly p = (fun _ : ℝ × ℝ => ((B0093.sqrtConst⁻¹ : ℝ) : ℂ)) *
      (wz ^ 2 * fun z : ℝ × ℝ => p.eval ((sz z : ℝ) : ℂ)) := by
    funext z
    simp [corePoly]
  rw [this]
  exact (Function.HasTemperateGrowth.const _).mul
    ((hasTemperateGrowth_wz.pow 2).mul (hasTemperateGrowth_eval_sz p))

/-- `U_G` of the core function `r² p(r²) e^{-r²/4} e^{2iϑ}`, as a Schwartz function. -/
def coreS (p : ℂ[X]) : 𝓢(ℝ × ℝ, ℂ) :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) (hasTemperateGrowth_corePoly p) gaussS

theorem coreS_apply (p : ℂ[X]) (z : ℝ × ℝ) :
    coreS p z = ((B0093.sqrtConst⁻¹ : ℝ) : ℂ) * (wz z ^ 2 * p.eval ((sz z : ℝ) : ℂ)) *
      (Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) : ℂ) := by
  rw [coreS, SchwartzMap.bilinLeftCLM_apply]
  simp only [ContinuousLinearMap.lsmul_apply, gaussS_apply, corePoly, Complex.real_smul]
  ring

/-- `coreS p = U_G (angularTwoField (profFun p))` (B0093's `conjG`, B0010's `angularTwoField`). -/
theorem coe_coreS (p : ℂ[X]) :
    ⇑(coreS p) = B0093.conjG (angularTwoField (profFun p)) := by
  funext z
  rw [B0093.conjG_eq]
  dsimp only
  rw [angularTwoField_profFun, coreS_apply]
  simp only [angF, qp, B0093.halfGaussian, Complex.real_smul]
  have hs : radiusSq z = sz z := rfl
  have hsz : sz z = z.1 ^ 2 + z.2 ^ 2 := rfl
  have hc : B0093.sqrtConst ≠ 0 := B0093.sqrtConst_pos.ne'
  have he : Real.exp (-(sz z / 4)) =
      Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) * Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) := by
    rw [← Real.exp_add, hsz]
    congr 1
    ring
  have he8 : Real.exp (-(radiusSq z / 8)) = Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) := by
    rw [hs, hsz]
  have hpos : Real.exp (-((z.1 ^ 2 + z.2 ^ 2) / 8)) ≠ 0 := (Real.exp_pos _).ne'
  rw [he, he8, mul_inv]
  push_cast
  field_simp

/-- `U_G⁻¹ (coreS p)` is the core function `r² p(r²) e^{-r²/4} e^{2iϑ}`. -/
theorem conjGInv_coreS (p : ℂ[X]) :
    B0093.conjGInv ⇑(coreS p) = angularTwoField (profFun p) := by
  rw [coe_coreS, B0093.conjGInv_conjG]

end UnforcedLeray.B0094
