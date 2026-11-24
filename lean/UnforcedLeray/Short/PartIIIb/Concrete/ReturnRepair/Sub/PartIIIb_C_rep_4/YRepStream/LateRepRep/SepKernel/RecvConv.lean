import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.Exact
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.Holder
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.RecvConv.Lift

/-!
# `PartIII-b:C/rep/4/4/1/org/6/1/3`: `RepRecvConv` (receiver conversion)

Source `the November 2 reference manuscript` 5336, 5134-5139, 2683-2700, 4147.
Assembled from the exact multiplier (`RecvConv/Exact`), the lift identity (`RecvConv/Lift`) and the
Hoelder step (`RecvConv/Holder`) by `RecvConvOrg.repRecvConv_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem repRecvConv (dm dp : ℝ) : RepRecvConv dm dp :=
  RecvConvOrg.repRecvConv_of dm dp RecvConvOrg.recvExact RecvConvOrg.recvLift
    RecvConvOrg.recvHolder

end UnforcedLeray.Short.PartIIIb.Concrete
