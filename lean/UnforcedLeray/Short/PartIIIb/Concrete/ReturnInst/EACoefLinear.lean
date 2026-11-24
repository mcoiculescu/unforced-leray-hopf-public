import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.BmatLinear
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.EALinear

/-!
# `C/inst/7`: linearity of `b = s^{-1/2} E_A` in `A` (source 4971-4972, 4981, 4985)

`EAcoef = merOf (s^{-1/2} • (s^{3/2} • e_A))`. Linearity of `e_A` in `A` (`eALinear`) at `s > 0`
(with `B` linear by `bmatLinear`, the lattice summability by `eATermSummable`, and the
differentiability of `A^y` by `ayDiffAt`) transfers to `EAcoef` through the linearity of `merOf`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem eaCoefLinear (as : ℝ) (χf : ℝ → ℝ) (hχ : IsSourceCutoffC χf) : EACoefLinear as χf := by
  intro ν μ hν A A' r hA hA' p hp
  have hD : DifferentiableAt ℝ (Ay ν χf A) p.1 := ayDiffAt as χf hχ ν A hA p.1 hp
  have hD' : DifferentiableAt ℝ (Ay ν χf A') p.1 := ayDiffAt as χf hχ ν A' hA' p.1 hp
  obtain ⟨hB1, hB2⟩ := bmatLinear ν μ χf A A' r p.1 hD hD'
  have hS := eATermSummable ν μ χf A p.1 p.2 hν hp
  have hS' := eATermSummable ν μ χf A' p.1 p.2 hν hp
  obtain ⟨e1, e2⟩ := eALinear ν μ χf A A' r p.1 p.2 hB1 hB2 hS hS'
  have key : ∀ v : Vec3, (Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • (r • v))
      = r • ((Real.sqrt p.1)⁻¹ • (p.1 ^ (3 / 2 : ℝ) • v)) := by
    intro v
    module
  constructor
  · simp only [EAcoef, EA]
    rw [e1]
    simp only [smul_add, affMerOf_add]
  · simp only [EAcoef, EA]
    rw [e2, key, affMerOf_smul]

end UnforcedLeray.Short.PartIIIb.Concrete
