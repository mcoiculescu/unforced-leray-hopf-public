import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.InletProfileJets3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Shell.Main

/-!
# `inletENearJets : InletENearJets`

Source `the November 2 reference manuscript`
lines 2545-2549 (inlet cutoff vanishes near the axis), 1206-1222.  Assembled from the two leaves
`inletProfileJets3 : InletProfileJets3` and `nvShellJets : NvShellJets` via `inletENearJets_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`InletENearJets`** (source 2545-2549, 1206-1222). -/
theorem inletENearJets : InletENearJets :=
  inletENearJets_of inletProfileJets3 nvShellJets

end UnforcedLeray.Short.PartIIIb.Concrete
