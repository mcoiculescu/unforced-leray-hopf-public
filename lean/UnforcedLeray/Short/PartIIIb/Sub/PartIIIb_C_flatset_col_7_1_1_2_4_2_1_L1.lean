import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtInvH

/-!
# `sfcLiftEx`: every `g ∈ Hsp c` has a lift `f'` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/1`)

Source `the November 2 reference manuscript` 1650-1656.  The lift is the complex
transport `cplxH` of `NearInst.Body`, which is built from the velocity identity
`map cellPt (measureH c) = c • ageμ c (-3/2)` (`NearInst.Masked.cellPtH_aux`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcLiftEx : SFCLiftEx := by
  unfold SFCLiftEx
  intro c hc g
  refine ⟨UnforcedLeray.Short.PartIIIb.NearInst.Body.cplxH c
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_aux c hc) g, ?_⟩
  exact UnforcedLeray.Short.PartIIIb.NearInst.Body.cplxH_ae c
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_aux c hc) g

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
