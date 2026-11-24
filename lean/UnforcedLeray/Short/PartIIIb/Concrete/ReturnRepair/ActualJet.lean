import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_2

/-!
# `actualJet` (`PartIII-b:C/rep/6`, source 5389-5413, `repair:actual-jet`)

Discharges `actualJet` from the two kernel facts `jetEps1W` (`PartIII-b:C/rep/6/1`) and
`n0wLeN1` (`PartIII-b:C/rep/6/2`) through `actualJet_of` (`Sub/PartIII-b_C_rep_6.lean`).
Source of record: `the November 2 reference manuscript` lines 5389-5413.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`actualJet`** (`PartIII-b:C/rep/6`, `repair:actual-jet`, 5389-5413). -/
theorem actualJet (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ActualJet :=
  actualJet_of D hst (fun K chiO chiY => jetEps1W K chiO chiY) n0wLeN1

end UnforcedLeray.Short.PartIIIb.Concrete
