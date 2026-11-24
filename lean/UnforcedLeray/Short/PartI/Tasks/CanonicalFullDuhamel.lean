import UnforcedLeray.Short.PartI.Sub.PartI_C07_1_1
import UnforcedLeray.Short.PartI.Tasks.FullMildUnique
import UnforcedLeray.Short.PartI.Tasks.CoupledImpliesFullMild

/-!
# `PartI:C07/1/1`: the canonical full Duhamel identity

Source `the November 2 reference manuscript` lines 1094-1125. Composition of the
two leaves: `fullMildUnique` (Gronwall uniqueness for the full Duhamel equation, `PartI:C07/1/1/1`)
and `coupledImpliesFullMild` (coupled mild system implies the full Duhamel equation,
`PartI:C07/1/1/2`) through the existing `canonicalFullDuhamel_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem canonicalFullDuhamel : CanonicalFullDuhamel :=
  canonicalFullDuhamel_of fullMildUnique coupledImpliesFullMild

end UnforcedLeray.Short.PartI
