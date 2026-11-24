import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_regionsOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancelOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org

/-!
# `PlateauCancelSeq` from the leaves of the region split

Source `the November 2 reference manuscript` 4171-4214, 5303-5316.  The Prop
`SeqData.PlateauCancel` of `Sub/PartIII-b_C_rep_5_1_cancel/Bridge.lean` (organize
`PartIII-b:C/rep/5/1/cancel/org`) is `youngOldCancel_thin` of
`Sub/PartIII-b_C_rep_5_1_regionsOrg.lean`, whose inputs are the leaves `SepYoungThin`,
`ShiftedResolventThin` (`Org/YThinTrans.lean`, tasks `PartIII-b:C/rep/4/2/org/1-2`) and
`NearYoungOldZero` (`Org/FarThinParts.lean`, task `PartIII-b:C/rep/4/1/org/6`), shared with
`AgeError` (rep/4) and `AgeVelRep` (rep/5/2).  This file also checks that the thin chain of cancel/org
imports together with the region split of rep/4 and the repair chain of rep/5/2
(`Sub/PartIII-b_C_rep_5_2_1Org.lean`), as the final `AgeVelocity` file must.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The plateau cancellation along the sequence** (4171-4214, 5303-5316). -/
theorem plateauCancelSeq_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) (h1 : SepYoungThin dm dp)
    (h2 : ShiftedResolventThin dm dp) (h0 : NearYoungOldZero dm dp) :
    PlateauCancelSeq Pl σ₀ mZ dm dp :=
  fun D _ _ _ hst => youngOldCancel_thin D hst h1 h2 h0

end UnforcedLeray.Short.PartIIIb.Concrete
