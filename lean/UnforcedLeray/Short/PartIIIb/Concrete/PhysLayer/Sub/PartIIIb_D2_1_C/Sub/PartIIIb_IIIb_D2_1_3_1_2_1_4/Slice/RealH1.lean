import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.RealH1.Core
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.RealH1.TestBridge
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_4.Slice.RealH1.WeakDerBridge

/-!
# `sliceH1Real`: assembly of the real one-slice `H¹` bound

Source `the November 2 reference manuscript` lines 1351-1362.  The three
remaining source facts are proved in `RealH1/Core.lean` (`realH1Core`), `RealH1/TestBridge.lean`
(`realTestBridge`) and `RealH1/WeakDerBridge.lean` (`weakDerBridge`); this file assembles them
through `sliceH1Real_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sliceH1Real : SliceH1Real :=
  sliceH1Real_of realH1Core realTestBridge weakDerBridge

end UnforcedLeray.Short.PartIIIb.Concrete
