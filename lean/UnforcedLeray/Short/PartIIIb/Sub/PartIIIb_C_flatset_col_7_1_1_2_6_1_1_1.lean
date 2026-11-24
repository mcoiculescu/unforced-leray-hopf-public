import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_of
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH

/-!
# `FlatLift` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/1`)

Source `the November 2 reference manuscript`
1630-1645: `H = L²(s^{-3/2} ds dq/c dη)` on the cell, with the recentring `cellPt` carrying the
velocity measure `s^{-3/2} ds dq dη` to `c · s^{-3/2} ds dq/c dη`.  The lift `f ↦ merC ∘ f ∘ cellPt`
is `NearInst.Body.cplxH`, and its a.e. formula is `NearInst.Body.cplxH_ae`, both proved in
`NearInst/Body/Defs.lean` from the change-of-variables identity `Masked.cellPtH_eq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatLift : FlatLift := by
  unfold FlatLift
  intro c hc f
  exact ⟨UnforcedLeray.Short.PartIIIb.NearInst.Body.cplxH c
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_eq c hc) f,
    UnforcedLeray.Short.PartIIIb.NearInst.Body.cplxH_ae c
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_eq c hc) f⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
