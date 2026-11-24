import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3

/-!
# `PartIII-b:C/grad/3/3`: `A^y = χ_f A` is `C^2` (source 4741-4745, 4955-4962)

The target `AyContDiffAt2 as χf` quantifies over every `χf : ℝ → ℝ`. For a discontinuous `χf`
it is false: `A^y(s) = χf(νs) A(s)` is then discontinuous at a point where `A(s) ≠ 0`. The
provable statement carries the source cutoff hypothesis `IsSourceCutoffC χf` (smooth profile,
source 4953-4955), as in `AyDiffAt`/`AyDerivBound` of the sibling leaves.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The corrected leaf: `A^y = χ_f A` is `C^2` at each `s > 0` for `χ_f` the smooth source
cutoff and `A ∈ 𝒜` (`C^6` on `(0,∞)`, source 4741-4745). -/
theorem ayContDiffAt2 (as : ℝ) (χf : ℝ → ℝ) : AyContDiffAt2 as χf := by
  intro hχ ν A hA s hs
  have h1 : ContDiffAt ℝ 2 (fun t => χf (ν * t)) s :=
    ((hχ.smooth.comp (contDiff_const.mul contDiff_id)).contDiffAt).of_le (by norm_num)
  have h2 : ContDiffAt ℝ 2 A s :=
    (hA.smooth.contDiffAt (isOpen_Ioi.mem_nhds hs)).of_le (by norm_num)
  exact h1.smul h2

end UnforcedLeray.Short.PartIIIb.Concrete
