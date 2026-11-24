import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields

/-!
# `C/inst/1`: `A^y = χ_f A` is differentiable at `s > 0` (source 4741-4745, 4953-4958)

`A ∈ 𝒜` is `C^6` on `(0,∞)` (`IsAffElem.smooth`), and `s ↦ χ_f(νs)` is `C^∞`
(`IsSourceCutoffC.smooth`), so their product is differentiable at every `s > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ayDiffAt (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : AyDiffAt as χf := by
  intro nu A hA s hs
  have hd : Differentiable ℝ χf := hχ.smooth.differentiable (by simp)
  have hl : DifferentiableAt ℝ (fun t : ℝ => nu * t) s := differentiableAt_id.const_mul nu
  have hc : DifferentiableAt ℝ (fun t : ℝ => χf (nu * t)) s := (hd (nu * s)).comp s hl
  have hAd : DifferentiableAt ℝ A s :=
    (hA.smooth.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hs)
  unfold Ay
  exact hc.smul hAd

end UnforcedLeray.Short.PartIIIb.Concrete
