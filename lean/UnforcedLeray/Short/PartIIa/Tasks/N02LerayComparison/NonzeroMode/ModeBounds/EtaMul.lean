import UnforcedLeray.Short.PartIIa.Sub.N02_4_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Commute

/-!
# Part II-a, task `PartII-a:N02/4/7/4`: the product rule in `η` and commutation of `S` with `η`

Target: `NzmbEtaMul` (`Sub/N02_4_7.lean`), source lines 1722-1727 of
`the November 2 reference manuscript`.
Uses `nzmb_iter_contDiff` from `Commute.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- Product rule for `y ↦ η g(y)` in an arbitrary direction `w`. -/
theorem nzmb_eta_fderiv (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (x w : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => (y.2 : ℂ) * g y) x w =
      (x.2 : ℂ) * fderiv ℝ g x w + g x * (w.2 : ℂ) := by
  have hc : HasFDerivAt (fun y : ℝ × ℝ => (y.2 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x hasFDerivAt_snd
  have hd : HasFDerivAt g (fderiv ℝ g x) x :=
    ((hg.differentiable (by simp)) x).hasFDerivAt
  have hm : HasFDerivAt (fun y : ℝ × ℝ => (y.2 : ℂ) * g y)
      ((x.2 : ℂ) • fderiv ℝ g x +
        g x • (Complex.ofRealCLM.comp (ContinuousLinearMap.snd ℝ ℝ ℝ))) x :=
    hc.mul hd
  rw [hm.fderiv]
  simp [Complex.ofRealCLM_apply]

/-- `nzS2 (η g) = η nzS2 g` pointwise. -/
theorem nzmb_eta_nzS2 (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    nzS2 (fun y : ℝ × ℝ => (y.2 : ℂ) * g y) x = (x.2 : ℂ) * nzS2 g x := by
  simp only [nzS2]
  rw [nzmb_eta_fderiv g hg x (1, 0)]
  simp only [Complex.ofReal_zero, mul_zero, add_zero, Complex.real_smul]
  ring

/-- Iterates: `S^[n] (η g) = η S^[n] g`. -/
theorem nzmb_eta_iter (n : ℕ) : ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g → ∀ x : ℝ × ℝ,
    (nzS2^[n] (fun y : ℝ × ℝ => (y.2 : ℂ) * g y)) x = (x.2 : ℂ) * (nzS2^[n] g) x := by
  induction n with
  | zero => intro g hg x; simp
  | succ n ih =>
    intro g hg x
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hfun : nzS2^[n] (fun y : ℝ × ℝ => (y.2 : ℂ) * g y)
        = fun y => (y.2 : ℂ) * (nzS2^[n] g) y :=
      funext fun y => ih g hg y
    rw [hfun, nzmb_eta_nzS2 _ (nzmb_iter_contDiff n g hg) x]

/-- Product rule in `η` and commutation of `S` with multiplication by `η`:
`∂_η(η g) = η ∂_η g + g`, `nzS2 (η g) = η nzS2 g` (since `∂_s η = 0`), and the iterate version. -/
theorem nzmbEtaMul : NzmbEtaMul := by
  intro g hg x
  refine ⟨?_, nzmb_eta_nzS2 g hg x, ?_⟩
  · have := nzmb_eta_fderiv g hg x (0, 1)
    simpa using this
  · intro n
    exact nzmb_eta_iter n g hg x

end UnforcedLeray.Short.PartIIa
