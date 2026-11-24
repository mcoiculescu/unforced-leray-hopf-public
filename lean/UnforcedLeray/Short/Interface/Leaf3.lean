import UnforcedLeray.Short.Interface.Sub.I05
import UnforcedLeray.Short.Interface.Leaf3.SlabBound
import UnforcedLeray.Short.Interface.Leaf3.PhaseHolder

/-!
# Interface leaf 3: the body force on a regular background is in `𝒴₂`

Source of record: `the November 2 reference manuscript`, lines 6071-6075.
The conditional assembly `bodyForceL3_of` (`Sub/I05.lean`) applied to the proved sub-lemmas.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.Interface

theorem bodyForceL3 : BodyForceL3 :=
  bodyForceL3_of slab_memLp_of_phase_bound phase_holder_sobolev

end UnforcedLeray.Short.Interface
