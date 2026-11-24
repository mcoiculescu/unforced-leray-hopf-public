import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarOf
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.FarBridge.TruncTendsto
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.SrcFinite
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarAbs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.Inv.FarId

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepYoungRepInv (dm dp : ℝ) : SepYoungRep dm dp :=
  sepYoungRepFar_of dm dp FarBridge.farOutTruncTendsto (fun Pl σ₀ mZ => sopSubIsFarSeq Pl σ₀ mZ dm dp) (sepOldSrcFinite dm dp) (sepFarAbs dm dp) (sepFarId dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
