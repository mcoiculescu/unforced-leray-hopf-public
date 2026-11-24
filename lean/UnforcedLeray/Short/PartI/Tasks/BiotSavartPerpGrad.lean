import UnforcedLeray.Short.PartI.Sub.S04
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad.DerivFormula
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad.DivFree
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad.Curl
import UnforcedLeray.Short.PartI.Tasks.BiotSavartPerpGrad.Decay

/-!
# Part I, task `PartI:S04/5`: the Biot-Savart velocity is `∇^⊥Ψ` (unconditional)

Source of record: `the November 2 reference manuscript`, lines 788-803.
The four facts `BiotSavartDerivFormula`, `BiotSavartDivFree`, `BiotSavartCurl`, `BiotSavartDecay`
are proved in the helper files `Tasks/BiotSavartPerpGrad/{DerivFormula,DivFree,Curl,Decay}.lean`
(tasks `PartI:S04/1-4`). The conditional theorem `biotSavart_eq_perpGrad_of` in `Sub/S04.lean`
then gives the statement. The hypothesis `hq0 : ∫ q = 0` is kept as stated and is not used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **`K q = ∇^⊥Ψ`** (source lines 788-803): for `q` smooth with Gaussian-class derivative
bounds, zero mean, and `Ψ` smooth with `ΔΨ = q` and `∇Ψ → 0` at infinity, the Biot-Savart
velocity `B0009.biotSavart q` equals `(-∂₂Ψ, ∂₁Ψ)` pointwise. -/
theorem biotSavart_eq_perpGrad {q Ψ : ℂ → ℂ} (hq : ContDiff ℝ ∞ q)
    (hqb : ∀ k : ℕ, ∃ C : ℝ, ∃ N : ℕ, ∀ y,
      ‖iteratedFDeriv ℝ k q y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))
    (hq0 : ∫ y, q y = 0) (hΨ : ContDiff ℝ ∞ Ψ)
    (hlap : ∀ y, iteratedFDeriv ℝ 2 Ψ y ![1, 1] +
      iteratedFDeriv ℝ 2 Ψ y ![Complex.I, Complex.I] = q y)
    (hdec : Filter.Tendsto (fderiv ℝ Ψ) (Filter.cocompact ℂ) (nhds 0)) :
    ∀ y, B0009.biotSavart q 0 y = -(fderiv ℝ Ψ y Complex.I) ∧
      B0009.biotSavart q 1 y = fderiv ℝ Ψ y 1 :=
  biotSavart_eq_perpGrad_of biotSavartDerivFormula biotSavartDivFree biotSavartCurl
    biotSavartDecay hq hqb hq0 hΨ hlap hdec

end UnforcedLeray.Short.PartI
