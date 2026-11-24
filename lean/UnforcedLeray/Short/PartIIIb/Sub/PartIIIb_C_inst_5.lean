import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.PsipADiff.Phi
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields

/-!
# `PartIII-b:C/inst/5`: `PsipADiff` reduced to the x-part and the s-part

Source `the November 2 reference manuscript` lines 4973-4980 (the sums and their
required derivatives converge by Gaussian decay), 4741-4745 (`A` is `C^6` on `(0,∞)`).
`psipA = Σ_j Φ(x_j)` (`psipA_eq_phi`, `Phi.lean`); differentiate the translate-sum in `x`, and in `s`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- x-part (lines 4978): the translate-sum `Σ_j Φ(x_j)` is differentiable in `x`
(Gaussian decay of `Φ` and `DΦ`, uniformly on a unit ball; `hasFDerivAt_tsum_of_isPreconnected`). -/
def PsiPhiXDiff : Prop :=
  ∀ (ν s : ℝ), 0 < ν → 0 < s → ∀ (M : Mat3) (x : ℝ × ℝ),
    DifferentiableAt ℝ (fun z : ℝ × ℝ => ∑' j : ℤ, psiPhi ν s M (xj ν j z)) x

/-- s-part (lines 4978, 4741-4745): `s' ↦ ψ^p_A(s', x)` is differentiable at `s > 0`
(`A^y` is `C^6` hence `C^1` on `(0,∞)`, `a(s') = 1+νs' ≥ 1`; Gaussian bounds uniform on
`[s/2, 2s]`; `hasDerivAt_tsum_of_isPreconnected`). -/
def PsipASDiff (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ, 0 < s →
    ∀ x : ℝ × ℝ, DifferentiableAt ℝ (fun s' => psipA ν χf A s' x) s

theorem psipADiff_of (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf)
    (hx : PsiPhiXDiff) (hs : PsipASDiff as χf) : PsipADiff as χf := by
  intro ν hν A hA s hs0 x
  refine ⟨?_, hs hχ ν hν A hA s hs0 x⟩
  have ha : 0 < ageA ν s := by unfold ageA; positivity
  have : psipA ν χf A s = fun z : ℝ × ℝ => ∑' j : ℤ, psiPhi ν s (Ay ν χf A s) (xj ν j z) :=
    funext fun z => psipA_eq_phi ν χf A s z ha
  rw [this]
  exact hx ν s hν hs0 _ x

end UnforcedLeray.Short.PartIIIb.Concrete
