import UnforcedLeray.Short.Spine.Sub.SP_CAN4_4_1
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Spine: `OscProfContDiff` (leaf A1 of `Spine:SP-CAN/4/4/1`)

Proves `OscProfContDiff` (`Short/Spine/Sub/SP_CAN4_4_1.lean`) with the statement unchanged:
for every complex polynomial `p`, the profile `B0094.profFun p`, `r ↦ r² p(r²) e^{-r²/4}`, is
`C^∞` on all of `ℝ`.

Source of record: `the November 2 reference manuscript` line 1086 and lines
1134-1140 (Hermite decomposition of `D`; each eigenvector is a Gaussian-polynomial profile).

Route.

1. `z ↦ p.eval z` is `C^∞` over `ℂ` (`Polynomial.contDiff_aeval`), hence over `ℝ`
   (`ContDiff.restrict_scalars`).
2. `r ↦ (r : ℂ)` is `C^∞` over `ℝ` (`Complex.ofRealCLM`), so `r ↦ (r : ℂ)^2` is too, and
   `r ↦ p.eval ((r : ℂ)^2)` is `C^∞` by composition.
3. `r ↦ e^{-r²/4}` is `C^∞` over `ℝ` (`ContDiff.exp` of a polynomial), and its complex
   version `r ↦ ((e^{-r²/4} : ℝ) : ℂ)` is `C^∞` by composition with `Complex.ofRealCLM`.
4. Products (`ContDiff.mul`) give `B0094.profFun p`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Polynomial
open scoped ContDiff Topology InnerProductSpace

namespace UnforcedLeray.Short.Spine

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01
open UnforcedLeray.Cons.G3b

/-- **Leaf A1** (`OscProfContDiff`): `profFun p` is `C^∞` on `ℝ`. -/
theorem oscProfContDiff_proof : UnforcedLeray.Short.Spine.OscProfContDiff := by
  intro p
  -- polynomial evaluation is smooth over ℂ, hence over ℝ
  have hpolyC : ContDiff ℂ ∞ (fun x : ℂ => p.eval x) := by
    have h := Polynomial.contDiff_aeval (R := ℂ) (𝕜 := ℂ) p ∞
    simpa only [Polynomial.coe_aeval_eq_eval] using h
  have hpolyR : ContDiff ℝ ∞ (fun x : ℂ => p.eval x) :=
    ContDiff.restrict_scalars (𝕜 := ℝ) hpolyC
  -- r ↦ (r : ℂ), and its square
  have hr : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := by
    have e : (fun r : ℝ => (r : ℂ)) = (Complex.ofRealCLM : ℝ → ℂ) :=
      funext fun r => (Complex.ofRealCLM_apply r).symm
    rw [e]
    exact Complex.ofRealCLM.contDiff
  have hsq : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ) ^ 2) := hr.pow 2
  have hpoly : ContDiff ℝ ∞ (fun r : ℝ => p.eval ((r : ℂ) ^ 2)) := hpolyR.comp hsq
  -- r ↦ e^{-r²/4} (real valued), then its complex version
  have hq : ContDiff ℝ ∞ (fun r : ℝ => -(r ^ 2 / 4)) := by fun_prop
  have hexp : ContDiff ℝ ∞ (fun r : ℝ => Real.exp (-(r ^ 2 / 4))) := hq.exp
  have hgauss : ContDiff ℝ ∞ (fun r : ℝ => UnforcedLeray.B0094.gauss r) := by
    have e : (fun r : ℝ => UnforcedLeray.B0094.gauss r)
        = (Complex.ofRealCLM : ℝ → ℂ) ∘ (fun r : ℝ => Real.exp (-(r ^ 2 / 4))) := by
      funext r
      simp only [Function.comp_apply, Complex.ofRealCLM_apply, UnforcedLeray.B0094.gauss]
    rw [e]
    exact Complex.ofRealCLM.contDiff.comp hexp
  unfold UnforcedLeray.B0094.profFun
  exact (hsq.mul hpoly).mul hgauss

end UnforcedLeray.Short.Spine
