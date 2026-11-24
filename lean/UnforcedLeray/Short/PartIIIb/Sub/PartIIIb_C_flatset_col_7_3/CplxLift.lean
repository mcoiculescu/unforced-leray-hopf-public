import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3.Of
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll

/-!
# Complex lift (organizer task `PartIII-b:C/flatset/col/7/3/1`)

Source `the November 2 reference manuscript` 1641-1646, 1650-1656, 1684-1689.
Take `h' := cplxH c (cpcH_eq c hc) h`; `cplxH_ae` identifies it a.e. with `merC ∘ h ∘ cellPt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem cplxLift : CplxLift := by
  intro c hc h
  exact ⟨UnforcedLeray.Short.PartIIIb.NearInst.Body.cplxH c
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cpcH_eq c hc) h,
    UnforcedLeray.Short.PartIIIb.NearInst.Body.cplxH_ae c
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cpcH_eq c hc) h⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
