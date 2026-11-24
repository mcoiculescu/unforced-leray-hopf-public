import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.ChartBound.Core

/-!
# `PartIII-b:IIIb-D2/3/2/12/3/1`: `StrChartBound` from `StressCSRegion`

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

`strChartBound_proved_of` (in `PartIII-b_IIIb-D2_3_2_12_3_1`) reduces `StrChartBound` to the
Cauchy-Schwarz core `StressCSRegion`, and `stressCSRegion_proved` (in `ChartBound/Core`) proves that core.
-/

set_option autoImplicit false

theorem strChartBound_proved : UnforcedLeray.Short.PartIIIb.Concrete.StrChartBound :=
  UnforcedLeray.Short.PartIIIb.Concrete.strChartBound_proved_of
    UnforcedLeray.Short.PartIIIb.Concrete.stressCSRegion_proved
