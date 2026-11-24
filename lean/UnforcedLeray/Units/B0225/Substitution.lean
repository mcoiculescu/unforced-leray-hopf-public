import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import UnforcedLeray.Lib.SpecialFunctions.ComplexPowers

/-!
# B0225 helper: the substitution `σ = s e^{-t}`

Blueprint unit B0225 (label `eq:st18-t00118`), `paper/main.tex` lines 3379–3383, blueprint proof
outline: "substitute `σ = s e^{-t}` (`dt = -dσ/σ`, `e^{-μt} = (σ/s)^μ`, `s(1 - e^{-t}) = s - σ`).
The factor `σ` from `M_s` cancels `1/σ`."

For `s > 0`, `μ ∈ ℂ` and any `ψ : ℝ → E`:

  `∫_0^∞ e^{-μt} (se^{-t}) ψ(se^{-t}) dt = ∫_0^s (σ/s)^μ ψ(σ) dσ`        (`integral_substitution`)

and the left integrand is integrable on `(0, ∞)` iff the right one is integrable on `(0, s)`
(`integrableOn_substitution_iff`). Both hold for every `ψ` (one-dimensional change of variables,
Mathlib `integral_image_eq_integral_abs_deriv_smul`); `(σ/s)^μ` is the complex power of the
positive real `σ/s` (`Complex.cpow`, `(σ/s)^μ = e^{μ log(σ/s)}`, no branch issue).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter

namespace UnforcedLeray.B0225

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The age substitution `t ↦ σ = s e^{-t}`. -/
def ageSub (s t : ℝ) : ℝ := Real.exp (-t) * s

theorem hasDerivAt_ageSub (s t : ℝ) :
    HasDerivAt (ageSub s) (-(Real.exp (-t)) * s) t := by
  have h := ((hasDerivAt_neg t).exp).mul_const s
  have e : Real.exp (-t) * -1 * s = -(Real.exp (-t)) * s := by ring
  rw [e] at h
  exact h

theorem image_ageSub {s : ℝ} (hs : 0 < s) : ageSub s '' Ioi 0 = Ioo 0 s := by
  ext σ
  simp only [mem_image, mem_Ioi, mem_Ioo, ageSub]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨mul_pos (Real.exp_pos _) hs, ?_⟩
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    nlinarith
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log (s / σ), Real.log_pos ((one_lt_div h0).2 h1), ?_⟩
    rw [Real.exp_neg, Real.exp_log (div_pos hs h0)]
    field_simp

theorem injOn_ageSub {s : ℝ} (hs : 0 < s) : InjOn (ageSub s) (Ioi 0) := by
  intro a _ b _ h
  have h1 : Real.exp (-a) = Real.exp (-b) := mul_right_cancel₀ hs.ne' h
  have h2 := Real.exp_injective h1
  linarith

/-- The pointwise identity behind the substitution: `|dσ/dt| (σ/s)^μ ψ(σ) = e^{-μt} σ ψ(σ)`. -/
theorem substitution_pointwise {s : ℝ} (hs : 0 < s) (μ : ℂ) (ψ : ℝ → E) (t : ℝ) :
    |-(Real.exp (-t)) * s| • ((((ageSub s t) / s : ℝ) : ℂ) ^ μ • ψ (ageSub s t)) =
      Complex.exp (-(μ * t)) • ((Real.exp (-t) * s) • ψ (Real.exp (-t) * s)) := by
  have h1 : |-(Real.exp (-t)) * s| = Real.exp (-t) * s := by
    rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_pos hs]
  have h2 : (((ageSub s t) / s : ℝ) : ℂ) ^ μ = Complex.exp (-(μ * t)) := by
    rw [ageSub, mul_div_cancel_right₀ _ hs.ne',
      UnforcedLeray.Special.ofReal_cpow_eq_cexp (Real.exp_pos _), Real.log_exp]
    congr 1
    push_cast
    ring
  rw [h1, h2, smul_comm]
  rfl

/-- **`∫_0^∞ e^{-μt} (se^{-t}) ψ(se^{-t}) dt = ∫_0^s (σ/s)^μ ψ(σ) dσ`** for `s > 0`. -/
theorem integral_substitution {s : ℝ} (hs : 0 < s) (μ : ℂ) (ψ : ℝ → E) :
    ∫ t : ℝ in Ioi 0, Complex.exp (-(μ * t)) • ((Real.exp (-t) * s) • ψ (Real.exp (-t) * s)) =
      ∫ σ in (0 : ℝ)..s, ((σ / s : ℝ) : ℂ) ^ μ • ψ σ := by
  rw [intervalIntegral.integral_of_le hs.le, integral_Ioc_eq_integral_Ioo, ← image_ageSub hs,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (hasDerivAt_ageSub s t).hasDerivWithinAt) (injOn_ageSub hs)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  exact (substitution_pointwise hs μ ψ t).symm

/-- The integrability counterpart of `integral_substitution`. -/
theorem integrableOn_substitution_iff {s : ℝ} (hs : 0 < s) (μ : ℂ) (ψ : ℝ → E) :
    IntegrableOn (fun t : ℝ =>
        Complex.exp (-(μ * t)) • ((Real.exp (-t) * s) • ψ (Real.exp (-t) * s))) (Ioi 0) ↔
      IntervalIntegrable (fun σ => ((σ / s : ℝ) : ℂ) ^ μ • ψ σ) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le, integrableOn_Ioc_iff_integrableOn_Ioo,
    ← image_ageSub hs, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun t _ => (hasDerivAt_ageSub s t).hasDerivWithinAt) (injOn_ageSub hs)]
  exact integrableOn_congr_fun (fun t _ => (substitution_pointwise hs μ ψ t).symm)
    measurableSet_Ioi

end UnforcedLeray.B0225
