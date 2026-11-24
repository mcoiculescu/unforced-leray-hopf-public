import UnforcedLeray.Short.PartI.Sub.T02_3

/-!
# Part I, task `PartI:T02/3`: `ReflectBoundedDerivs` (leaf of `ClassicalOdd`)

Source of record: `the November 2 reference manuscript`, line 288 ("Uniqueness gives
`v(-q,-eta,s) = -v(q,eta,s)`"). The Prop `ReflectBoundedDerivs` is defined in
`Short/PartI/Sub/T02_3.lean`: reflection `reflV v s z = -v s (-z)` maps a velocity field with all
spatial derivatives bounded on `[0,T]` to one with the same bounds.

## What is proved here

`reflectBoundedDerivs : ReflectBoundedDerivs`. The same constant `M` works: the `k`-th derivative of
`reflV v s` at `z` has the norm of the `k`-th derivative of `v s` at `-z`. The proof writes
`reflV v s = -(v s ∘ neg)` (with `neg = LinearIsometryEquiv.neg ℝ`), removes the outer sign by
`iteratedFDeriv_neg_apply` and `norm_neg`, and removes the composition by the linear isometry by
`LinearIsometryEquiv.norm_iteratedFDeriv_comp_right`. The identical reflection identity is proved in
`Units/B0145.lean` (`norm_jet_reflect`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- Reflection of bounded derivatives: if every spatial derivative of `v` is bounded on `[0,T]`,
so is every spatial derivative of the reflected field `reflV v`, with the same bound. -/
theorem reflectBoundedDerivs : ReflectBoundedDerivs := by
  intro T v hv k
  obtain ⟨M, hM⟩ := hv k
  refine ⟨M, fun s hs z => ?_⟩
  have e : reflV v s = -(v s ∘ (LinearIsometryEquiv.neg ℝ : Plane ≃ₗᵢ[ℝ] Plane)) := by
    funext w
    rfl
  rw [e, iteratedFDeriv_neg_apply, norm_neg,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
  exact hM s hs (-z)

end UnforcedLeray.Short.PartI
