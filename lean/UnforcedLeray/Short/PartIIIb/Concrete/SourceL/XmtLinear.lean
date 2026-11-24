import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8.Smul
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8.NewtonAdd
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_8.StreamTail

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem xmtLinear : XmtLinear :=
  xmtLinear_of xmtSmul newtonV_add streamTail_int

end UnforcedLeray.Short.PartIIIb.Concrete
