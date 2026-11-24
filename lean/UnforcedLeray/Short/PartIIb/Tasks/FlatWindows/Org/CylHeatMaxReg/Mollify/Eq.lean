import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4_3_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg.Mollify.LocInt

/-!
# Part II-b, task `PartII-b:T13/1/4/3/2` (`chmMollEq`): weak equation for the mollified window

Source: `the November 2 reference manuscript` (SP) lines 1933-1935.

Proof. Compose the reduction `chmMollEq_of : ChmLocInt → ChmMollEq` with the leaf `chmLocInt`.
-/

set_option autoImplicit false

theorem chmMollEq : UnforcedLeray.Short.IIb.ChmMollEq := by
  exact UnforcedLeray.Short.IIb.chmMollEq_of UnforcedLeray.Short.IIb.chmLocInt
