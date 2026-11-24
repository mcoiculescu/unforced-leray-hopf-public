import UnforcedLeray.Short.PartIIIb.Concrete.ReturnAff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps

/-!
# The two source-cutoff predicates agree (source 4750-4752, 4953-4955)

`ReturnAff.IsSourceCutoff` (now `C^∞`, `((⊤ : ℕ∞) : WithTop ℕ∞)`) and
`ReturnOps.IsSourceCutoffC` state the same source cutoff `χ̂_f`: smooth, one on `t ≤ 1`, zero on
`t ≥ 1.1`, values in `[0,1]`.  Both are satisfied by `sourceCutoffStd`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem isSourceCutoffC_iff (χ : ℝ → ℝ) : IsSourceCutoffC χ ↔ IsSourceCutoff χ :=
  ⟨fun h => ⟨h.smooth, h.one, h.zero, h.range⟩, fun h => ⟨h.smooth, h.one, h.zero, h.range⟩⟩

theorem isSourceCutoffC_std : IsSourceCutoffC sourceCutoffStd :=
  (isSourceCutoffC_iff _).2 isSourceCutoff_std

end UnforcedLeray.Short.PartIIIb.Concrete
