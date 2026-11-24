import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2_2.Far
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_4_2_org_1_1_2_2.FarFin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge.TruncTendsto
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarAbs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarId

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepInvYoung (dm dp : ℝ) : SepInvYoung dm dp :=
  sepInvYoungFar_of dm dp FarBridge.farOutTruncTendsto
    (fun Pl σ₀ mZ => sopSubIsFarSeq Pl σ₀ mZ dm dp) (sepThinSrcFinite dm dp)
    (sepFarAbs dm dp) (sepFarId dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
