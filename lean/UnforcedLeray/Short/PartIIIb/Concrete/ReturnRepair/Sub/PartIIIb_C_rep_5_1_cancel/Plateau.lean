import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_regionsOrg.Plateau
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.SepYoung
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.FarThin.NearYoungOld

/-!
# `PartIII-b:C/rep/5/1/cancel/1`: `PlateauCancelSeq`

One-line application of `plateauCancelSeq_of` (`Sub/PartIII-b_C_rep_5_1_regionsOrg/Plateau.lean`)
to `sepYoungThin` (`Org/YThinTrans/SepYoung.lean`), `shiftedResolventThin`
(`Org/YThinTrans/ShiftedResolvent.lean`), and `nearYoungOldZero` (`Org/FarThin/NearYoungOld.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem plateauCancelSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) :
    PlateauCancelSeq Pl σ₀ mZ dm dp :=
  plateauCancelSeq_of Pl σ₀ mZ dm dp (sepYoungThin dm dp) (shiftedResolventThin dm dp)
    (nearYoungOldZero dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
