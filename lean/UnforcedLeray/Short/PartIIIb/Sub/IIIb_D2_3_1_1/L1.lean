import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L7
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L9

/-!
# `oldSourceReg_all` (`PartIII-b:IIIb-D2/3/1/1/1`, unconditional `OldSourceReg`)

Source of record: `the November 2 reference manuscript` 4155-4171, 2666-2703,
3611-3621. `OldSourceReg` (`Sub/IIIb-D2_3_1_1.lean`) is proved unconditionally by
`oldSourceReg_of` from the five leaves `chartOfNullPullback` (L1), `sepWCongrAE` (L2),
`oldCutMeasurable` (L3), `oldCutMoment` (L7) and `strChartL2` (L9) of `Sub/IIIb-D2_3_1_1_1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`OldSourceReg` holds unconditionally** (source 4155-4171, 2666-2703, 3611-3621). -/
theorem oldSourceReg_all (c mZ ρb γ ν ε : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) :
    OldSourceReg c mZ ρb γ ν ε hχo :=
  oldSourceReg_of chartOfNullPullback sepWCongrAE oldCutMeasurable oldCutMoment strChartL2
    c mZ ρb γ ν ε hχo

end UnforcedLeray.Short.PartIIIb.Concrete
