import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThinBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.NearYoungOld
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinThin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.LateThinRep
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.EarlyThinThin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.EarlyThinRep

/-!
# `PartIII-b:C/rep/4/1`: `ageLateEarlyThin`

Source `the November 2 reference manuscript` 5301-5372, 5607-5627.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageLateEarlyThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeLateEarlyThin Pl σ₀ mZ dm dp :=
  ageLateEarlyThin_of Pl σ₀ mZ dm dp (nearYoungOldZero dm dp)
    (farLateThinThin Pl σ₀ mZ dm dp) (farLateThinRep Pl σ₀ mZ dm dp)
    (farEarlyThinThin Pl σ₀ mZ dm dp) (farEarlyThinRep Pl σ₀ mZ dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
