import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQIbp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQYq

/-!
# `GEQuad` (assembly, source 2525-2533, 2562-2564)

Direct application of `gEQuad_of` (in `GEQuadSub/Defs.lean`) to the accepted leaves
`gEQIbp` (weak integration by parts, `GEQuadSub/GEQIbp.lean`) and `gEQYq`
(`F ∈ Y_{q₀}`, `GEQuadSub/GEQYq.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gEQuad : GEQuad :=
  gEQuad_of gEQIbp gEQYq

end UnforcedLeray.Short.PartIIIb.Concrete
