import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Core

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3`: the sequence bin bound `WardYMajBinSeq`

Source `the November 2 reference manuscript` 5585-5593.

`wardYMajBinSeq` is `wardYMajBinSeq_of` applied to the proved core `wardYMajBinCore`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Target**: `WardYMajBinSeq` from the proved core (source 5585-5593). -/
theorem wardYMajBinSeq (D : SeqData) {dm dp : ℝ} : D.WardYMajBinSeq dm dp :=
  wardYMajBinSeq_of D wardYMajBinCore

end UnforcedLeray.Short.PartIIIb.Concrete

end
