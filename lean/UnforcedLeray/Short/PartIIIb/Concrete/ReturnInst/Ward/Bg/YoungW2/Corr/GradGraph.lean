import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradY
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq

/-!
# `BgCorrGradGraph` (source 2525-2541)

Task `PartIII-b:C/ward/12/3/1`. Source of record
`the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgCorrGradGraph : BgCorrGradGraph :=
  bgCorrGradGraph_of bgCorrGradY bgCorrGradEq

end UnforcedLeray.Short.PartIIIb.Concrete
