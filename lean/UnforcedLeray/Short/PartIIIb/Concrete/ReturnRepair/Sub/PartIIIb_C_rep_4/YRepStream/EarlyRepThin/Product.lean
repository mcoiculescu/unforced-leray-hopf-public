import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4_4_1_org_7_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4_4_1_org_7_2.EarlyPhasePointwise
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4_4_1_org_7_2.EarlyVelSliceMeas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4_4_1_org_7_2.EarlyVelPhysL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.RbFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.HolderPhase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_1.PeriodSmall

/-!
# `PartIII-b:C/rep/4/4/1/org/7/2` (`earlyRepThinProduct`), assembly

Source `the November 2 reference manuscript` 5169-5176. The target is obtained by
applying the decomposition theorem `earlyRepThinProduct_of` to the proved leaves
`earlyPhasePointwise`, `earlyVelSliceMeas`, `earlyVelPhysL2` (Sub/PartIII-b_C_rep_4_4_1_org_7_2/)
and `rbFacts`, `holderPhase`, `periodSmall` (Sub/PartIII-b_C_rep_1/).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem earlyRepThinProduct (Pl : PlanarData) (σ₀ mZ dm dp : ℝ) : EarlyRepThinProduct Pl σ₀ mZ dm dp :=
  earlyRepThinProduct_of Pl σ₀ mZ dm dp rbFacts earlyPhasePointwise earlyVelSliceMeas holderPhase
    earlyVelPhysL2 periodSmall

end UnforcedLeray.Short.PartIIIb.Concrete
