import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancelOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancel.Plateau
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.SopSubIsFar
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1.VanishAbove
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_2

/-!
# `PartIII-b:C/rep/5/1`: `AgeVelThin`

Source `the November 2 reference manuscript` lines 5303-5316, 5594-5599, 5688-5689.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageVelThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeVelThin Pl σ₀ mZ dm dp :=
  ageVelThin_of_pieces Pl σ₀ mZ dm dp (farBins Pl σ₀ mZ dm dp) (wardLateBinSeq Pl σ₀ mZ dm dp)
    (plateauCancelSeq Pl σ₀ mZ dm dp) (sopSubIsFarSeq Pl σ₀ mZ dm dp)
    (farVanishAboveSeq Pl σ₀ mZ dm dp) (fun D _ _ _ h => wardOutSupported D h) binTriangle

end UnforcedLeray.Short.PartIIIb.Concrete

end
