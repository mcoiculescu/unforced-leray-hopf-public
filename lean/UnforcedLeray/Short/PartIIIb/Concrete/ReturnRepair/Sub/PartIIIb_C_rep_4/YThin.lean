import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.SepYoung
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Table
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.Margin

/-!
# `PartIII-b:C/rep/4/2`: `ageYThin` (`AgeTransThin`)

Source `the November 2 reference manuscript` 5312-5316, 5333-5340, 5357-5367,
5607-5627. Assembles the thin stream-transition leaf `AgeTransThin` from `sepYoungThin`,
`shiftedResolventThin`, `transThinTable`, `transThinOpTable_of`, and `ageTransThin_of_table`.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem ageYThin (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : AgeTransThin Pl σ₀ mZ dm dp := by
  exact ageTransThin_of_table (transThinOpTable_of (sepYoungThin dm dp)
    (shiftedResolventThin dm dp) (transThinTable Pl σ₀ mZ dm dp))

end UnforcedLeray.Short.PartIIIb.Concrete

end
