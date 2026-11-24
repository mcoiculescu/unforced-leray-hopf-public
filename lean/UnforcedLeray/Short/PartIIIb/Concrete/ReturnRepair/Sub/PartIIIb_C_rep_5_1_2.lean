import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_cancelOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4

/-!
# `PartIII-b:C/rep/5/1/2`: `WardLateBinSeq`

Source `the November 2 reference manuscript` lines 5585-5605, 5688-5689.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardLateBinSeq (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : WardLateBinSeq Pl σ₀ mZ dm dp := by
  intro D _ _ _ h
  exact wardLateBin D h

end UnforcedLeray.Short.PartIIIb.Concrete

end
