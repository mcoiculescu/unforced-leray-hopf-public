import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.NearYoungOld

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem ageVelRep (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeVelRep Pl σ₀ mZ dm dp :=
  ageVelRep_of_regions Pl σ₀ mZ dm dp (ageVelFarRep Pl σ₀ mZ dm dp)
    (ageVelTransRep Pl σ₀ mZ dm dp) (nearYoungOldZero dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
