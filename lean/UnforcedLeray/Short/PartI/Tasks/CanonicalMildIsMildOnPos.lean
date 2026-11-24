import UnforcedLeray.Short.PartI.Sub.PartI_C07_1
import UnforcedLeray.Short.PartI.Tasks.CanonicalFullDuhamel

/-!
# `PartI:C07/1`: the canonical mild solution is mild on `(0,∞)`

Source `the November 2 reference manuscript` lines 1094-1125. The target is the
definition-level statement `CanonicalMildIsMildOnPos` (`Sub/PartI_C07.lean`). It is discharged by
the cocycle extension `canonical_mild_is_mild_on_pos_of` (`Sub/PartI_C07_1.lean`) applied to the
Duhamel identity `canonicalFullDuhamel` (`PartI:C07/1/1`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem canonical_mild_is_mild_on_pos : CanonicalMildIsMildOnPos :=
  canonical_mild_is_mild_on_pos_of canonicalFullDuhamel

end UnforcedLeray.Short.PartI
