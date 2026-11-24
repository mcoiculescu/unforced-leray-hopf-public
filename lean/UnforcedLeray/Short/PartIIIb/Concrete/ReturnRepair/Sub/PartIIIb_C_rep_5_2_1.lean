import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.NearSplit
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.RepFarBox
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.RepFarExt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.YoungCutLate
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.VelGLeSrc
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.RepSplitAE
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.RepSrcEarly
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.RepMargin

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem ageVelFarRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeVelFarRep Pl σ₀ mZ dm dp :=
  ageVelFarRep_of Pl σ₀ mZ dm dp (fun D _ _ _ hst => seqNearSplitStanding D hst) repFarBox repFarExt
    youngCutLate velGLeSrc repSplitAE (fun D _ _ _ hst => repSrcEarly D hst) (repMargin Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
