import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Data.Meas
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Data.Bound

/-!
# `PartII-b:T13/1/7/1`: the window data (`WbdData`)

Source: `the November 2 reference manuscript` lines 1928-1933.

Assembles `wbdData_of` from the measurability (`wbddMeas`) and the weighted bounds (`wbddBound`).
-/

set_option autoImplicit false

noncomputable section

theorem wbdData : UnforcedLeray.Short.IIb.WbdData :=
  UnforcedLeray.Short.IIb.wbdData_of wbddMeas wbddBound
