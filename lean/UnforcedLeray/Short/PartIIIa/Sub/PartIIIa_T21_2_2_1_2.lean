import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1

/-!
# Decomposition of `PartIII-a:T21/2/2/1/2` (`AdjF0Cont`)

Source: `the November 2 reference manuscript` 3060-3071, 2854-2865.
`E_0(r) = ∫_{C_d} p_d⁻¹ |a⁻¹ φ(r, √a ·)|²` with `d = c/√a`.  Substituting `x = √a y`
(two dimensions, `dy = dx / a`; `sin(π y₁/d) = sin(π x₁/c)`) gives
`E_0(r) = a⁻³ ∫_{C_c} (1 + x₂²/a + (c/π)² sin²(π x₁/c)/a)^{-m} |φ(r,x)|² dx`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The fixed-cell weight `(1 + x₂²/a + (c/π)² sin²(π x₁/c)/a)^{-m}` after the substitution
`x = √a y` (the periodic weight `p_d⁻¹` at the scaled point). -/
def wtF0 (c m a : ℝ) (x : ℝ × ℝ) : ℝ :=
  (1 + x.2 ^ 2 / a + (c / Real.pi) ^ 2 * Real.sin (Real.pi * x.1 / c) ^ 2 / a) ^ (-m)

/-- The fixed-cell energy integral `∫_{C_c} wtF0 |φ(r)|²`, as a function of the age `r`. -/
def coreF0 (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ) : ℝ :=
  ∫ x in B0579.cell c, wtF0 c m (clockA ν r) x * ‖φ r x‖ ^ 2

/-- (i) Change of variables (SP 2854-2865, 3060-3071): for `a = 1 + ν r > 0` and `c > 0`,
`adjF0 ν c m φ r = a⁻³ · coreF0 ν c m φ r`. -/
def AdjF0Ident : Prop :=
  ∀ (ν c m : ℝ) (φ : ℝ → ℝ × ℝ → ℂ) (r : ℝ), 0 < c → 0 < clockA ν r →
    adjF0 ν c m φ r = (clockA ν r)⁻¹ ^ 3 * coreF0 ν c m φ r

/-- (ii) Continuity of the fixed-cell energy on `[t, s]` for an adjoint flow (SP 3060-3071):
`wtF0 c m a x / density(-m) x` is bounded above and below uniformly for `a` in a compact subset of
`(0, ∞)` and continuous in `a`; `φ r' → φ r` in `L²(cellMeasure c (-m))` by `strongCont`;
dominated convergence plus the Cauchy-Schwarz bound for `|φ r'|² - |φ r|²`. -/
def AdjF0Core : Prop :=
  ∀ (ν c m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) (t s : ℝ) (g : ℝ × ℝ → ℂ)
    (φ : ℝ → ℝ × ℝ → ℂ), 0 < ν → 0 < c → 0 ≤ t → t < s →
    IsAdjointFlow ν c m tr t s g φ → ContinuousOn (coreF0 ν c m φ) (Icc t s)

theorem adjF0Cont_of (h1 : AdjF0Ident) (h2 : AdjF0Core) : AdjF0Cont := by
  intro ν c m tr t s g φ hν hc ht hts hφ
  have hpos : ∀ r ∈ Icc t s, 0 < clockA ν r := by
    intro r hr
    unfold clockA
    have : 0 ≤ r := ht.trans hr.1
    positivity
  have hcore := h2 ν c m tr t s g φ hν hc ht hts hφ
  have hinv : ContinuousOn (fun r => (clockA ν r)⁻¹ ^ 3) (Icc t s) := by
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀
    · unfold clockA; fun_prop
    · exact fun r hr => (hpos r hr).ne'
  refine (hinv.mul hcore).congr ?_
  intro r hr
  exact h1 ν c m φ r hc (hpos r hr)

end UnforcedLeray.Short.IIIa
