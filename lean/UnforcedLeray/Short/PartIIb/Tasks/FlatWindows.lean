import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_4
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Core
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Sub
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.ClassSub

/-!
# Part II-b, task `PartII-b:T13` (`flat_graph_bound`): assembly

Source of record: `the November 2 reference manuscript` (SP) lines 1912-1938.
Composition `flatGraphBound_of_per` (the corrected congruence step `graphBoundCongrPer`, which needs
the periodicity supplied by `InFlatClass` through `InHr`) of the four leaves `flatGraphExists`,
`flatResponseSub`, `flatClassSub`, `graphBoundCongrPer`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem flat_graph_bound : ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 →
    ∃ C : ℝ, ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ F : CProf, InHr c r F → ∀ b : CProf,
      IsFlatResponse ν μ F b → InFlatClass c r b → GraphBound ν c r 0 C F b :=
  flatGraphBound_of_per flatGraphExists flatResponseSub flatClassSub graphBoundCongrPer

end UnforcedLeray.Short.IIb

end
