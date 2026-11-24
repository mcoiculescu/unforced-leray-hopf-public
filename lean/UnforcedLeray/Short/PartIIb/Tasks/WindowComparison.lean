import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G3
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.BoxCutoff
import UnforcedLeray.Short.PartIIb.Tasks.WindowComparison.TransverseTail

/-!
# Part II-b, task `PartII-b:G3`: Intermediate age-window operator comparison (`WindowComparison`, SP 2438–2463)

Source of record: `the November 2 reference manuscript` (SP), lines 2438–2463:
Assembles `WindowComparison` (`PartII-b:G3`) from:
* `windowBoxCutoffBound_proof : WindowBoxCutoffBound` (`PartII-b:G3/1`, `Tasks/WindowComparison/BoxCutoff.lean`),
* `windowTransverseTailBound_proof : WindowTransverseTailBound` (`PartII-b:G3/2`, `Tasks/WindowComparison/TransverseTail.lean`),
* `LocalInteractionComparison` (`PartII-b:T20`), and
* `YoungLateOperatorBounds` (`PartII-b:G2`),
via `windowComparison_of_box_tail` in `Sub/PartII-b_G3.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- **`PartII-b:G3` (`WindowComparison`, SP 2438–2463)**: intermediate age-window comparison on
`[σ, S] = [ε^a, ε^{-b}]` from `LocalInteractionComparison` (`h20`) and `YoungLateOperatorBounds` (`h2`). -/
theorem windowComparison_of
    (h20 : UnforcedLeray.Short.IIb.LocalInteractionComparison)
    (h2 : UnforcedLeray.Short.IIb.YoungLateOperatorBounds) :
    UnforcedLeray.Short.IIb.WindowComparison :=
  windowComparison_of_box_tail windowBoxCutoffBound_proof windowTransverseTailBound_proof h20 h2

end UnforcedLeray.Short.IIb

end
