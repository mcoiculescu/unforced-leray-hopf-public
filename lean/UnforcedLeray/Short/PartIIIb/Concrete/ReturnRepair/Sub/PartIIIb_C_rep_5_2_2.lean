import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.ShiftedResolventRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.OldRepIsRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransVanishOff
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.LateVelGain
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransSepChart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.RepMargin

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageVelTransRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeVelTransRep Pl σ₀ mZ dm dp :=
  ageVelTransRep_of Pl σ₀ mZ dm dp (sepYoungRep dm dp) (shiftedResolventRep dm dp)
    oldRepIsRep transVanishOff lateVelGain transSepChart (repMargin Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
