import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepThinOrg.EarlyThinBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.ProductFull

/-!
# `PartIII-b:C/rep/4/4/1/org/5/org` (e): both thin-receiver repair entries from the one kernel leaf

Source `the November 2 reference manuscript` 5303-5308, 5318-5319, 5323-5338,
5169-5176.

With `repair:source` for the unlocalised repair stress proved (`repairProductAll`,
`LateRepRep/ProductFull.lean`, task `PartIII-b:C/rep/4/4/1/org/6/2`) and the multiplier commutation
proved (`multYoung`), the late-output thin entry `LateRepThin` and the early-source kernel estimate
`EarlyRepThinKernel` both follow from the single far-kernel leaf `FarRepThinUng`
(`lateRepThin_of_farRepThinUng`, `earlyRepThinKernel_of_farRepThinUng`).
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`LateRepThin` from the far-kernel leaf alone** (source 5318, 5323-5338, 5169-5176). -/
theorem lateRepThin_of_farRepThinUng (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (hA : FarRepThinUng Pl σ₀ mZ dm dp) : LateRepThin Pl σ₀ mZ dm dp :=
  lateRepThin_of Pl σ₀ mZ dm dp hA (repairProductAll dm dp)

end UnforcedLeray.Short.PartIIIb.Concrete
