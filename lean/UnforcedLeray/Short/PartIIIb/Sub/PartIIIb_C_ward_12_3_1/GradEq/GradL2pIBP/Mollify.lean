import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_2.L4

/-!
# `GradL2pMollify`: gated slice mollification

Source `the November 2 reference manuscript`
lines 2531, 1415-1424.  Assembled from the mollifier sequence (`mollSeqExists`), the slice facts
(`mollSliceFacts`), the derivative identity (`mollDerivIdentity`) and the convergence
(`mollConv`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradL2pMollify : GradL2pMollify :=
  gradL2pMollify_of mollSeqExists mollSliceFacts mollDerivIdentity mollConv

end UnforcedLeray.Short.PartIIIb.Concrete
