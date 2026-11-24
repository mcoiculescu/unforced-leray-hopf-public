import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.BmatLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.FALinear

/-!
# `C/inst/6`: linearity of `b = s^{-1/2} F_A` in `A` (source 4970, 4981, 4985)

`FAcoef = merOf (s^{-1/2} • (s^{3/2} • f_A))`. Linearity of `f_A` in `A` (`fALinear`) at `s > 0`
(with `B` linear by `bmatLinear`, the lattice summability by `fATermSummable`, and the
differentiability of `A^y` by `ayDiffAt`) transfers to `FAcoef` through the linearity of `merOf`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem faCoefLinear (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : FACoefLinear as χf := by
  intro ν μ hν A A' r hA hA' p hp
  have hD : DifferentiableAt ℝ (Ay ν χf A) p.1 := ayDiffAt as χf hχ ν A hA p.1 hp
  have hD' : DifferentiableAt ℝ (Ay ν χf A') p.1 := ayDiffAt as χf hχ ν A' hA' p.1 hp
  obtain ⟨hB1, hB2⟩ := bmatLinear ν μ χf A A' r p.1 hD hD'
  have hS := fATermSummable ν μ χf A p.1 p.2 hν hp
  have hS' := fATermSummable ν μ χf A' p.1 p.2 hν hp
  obtain ⟨f1, f2⟩ := fALinear ν μ χf A A' r p.1 p.2 hB1 hB2 hS hS'
  have key : ∀ v : Vec3, (Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • (r • v))
      = r • ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • v)) := by
    intro v
    module
  constructor
  · simp only [FAcoef, FA]
    rw [f1]
    simp only [smul_add, affMerOf_add]
  · simp only [FAcoef, FA]
    rw [f2, key, affMerOf_smul]

end UnforcedLeray.Short.PartIIIb.Concrete
