import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasWard
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasXmt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanResMeasRaw
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.RawLiftRegularSeq

/-!
# Decomposition of `meanResMeas` (task `PartIII-b:C/rep/8/2/pres/6`)

Source `the November 2 reference manuscript`
lines 1205-1225 ("smooth through the axis for positive time"), 4139-4141, 4776-4791, 5272-5289.

The only missing source fact is the axis continuity of the raw coefficient along the sequence
(`AxisEv`); it needs the all-age decay of the actual train, which `IsBUCTrain` does not give.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Source 1205-1225 (`sct:lift`: the lift is smooth through the axis for positive time): for large
`n` the raw coefficient of the actual level `n` is continuous through the axis (its axis value
`axisExt` is the limit from off the axis). -/
def AxisEv (D : SeqData) (dm dp : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, D.IsActualLevel dm dp n → RawAxisContinuous D.Pl (D.level n)

theorem meanResMeas_of_axis (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hAx : AxisEv D dm dp) : D.MeanResMeas := by
  refine meanResMeas_of D ?_
  filter_upwards [hst.actual, hAx] with n hn hax z _
  exact wardDiffMeasAt_of_parts D.Pl D.K (D.level n) (D.mu n z) _ hn.profile hst.chiY
    (xmtMeasAt _ _ _ _) (rawLiftRegularAt D.Pl (D.level n) hn.buc (hax hn))

end UnforcedLeray.Short.PartIIIb.Concrete
