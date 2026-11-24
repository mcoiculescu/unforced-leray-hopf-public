import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineFields
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `C/inst/4`: summability of the lattice terms of `h^p_A` and `ψ^p_A` (source 4973-4978)

For fixed `ν, s > 0` and any `x`, the `j`-th terms of `h^p_A` and `ψ^p_A` are bounded by a fixed
constant times `(1 + |q - jc|)³ e^{-(q - jc)²/(4a)}` with `a = 1 + νs`, `c = ν⁻²`, and these
bounds are summable over `j ∈ ℤ`.  Only the fixed matrix `A^y(s)` enters, so no condition on `A`
beyond the definition of `HpPsiTermSummable` is used.  Helpers: `ReturnInst/HpPsiTermSummable/Gauss.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem hpPsiTermSummable : HpPsiTermSummable := by
  intro ν χ A s x hν hs
  have ha : 0 < ageA ν s := by
    unfold ageA
    nlinarith [mul_pos hν hs]
  have hc : 0 < cOf ν := by
    unfold cOf
    exact inv_pos.mpr (pow_pos hν 2)
  have hα : 0 < 1 / (4 * ageA ν s) := div_pos one_pos (by linarith)
  obtain ⟨K₁, hK₁⟩ := gp_hp_bound ν s ha (Ay ν χ A s) x
  obtain ⟨K₂, hK₂⟩ := gp_psi_bound ν s ha (Ay ν χ A s) x
  have hS := gp_poly_summable x.1 (1 / (4 * ageA ν s)) (cOf ν) hα hc
  refine ⟨Summable.of_norm_bounded (hS.mul_left K₁) (fun j => ?_),
    Summable.of_norm_bounded (hS.mul_left K₂) (fun j => ?_)⟩
  · exact hK₁ j
  · exact hK₂ j

end UnforcedLeray.Short.PartIIIb.Concrete
