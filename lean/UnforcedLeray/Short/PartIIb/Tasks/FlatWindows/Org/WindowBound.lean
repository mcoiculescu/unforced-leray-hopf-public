import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Data
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Transfer
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Norms
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Scalar

/-!
# `PartII-b:T13/1/7` the window bound (`WindowBound`)

Source: `the November 2 reference manuscript` lines 1928-1933.

Composition: the scalar window estimate `wbdScalar_of` (from the cut-off, heat, cylinder and
interpolation hypotheses and the window data, transfer and norm leaves) followed by the passage
from components to the meridional vector `windowBound_of_scalar`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem windowBound_of (h1 : UnforcedLeray.Short.IIb.WinCutProps) (h2 : UnforcedLeray.Short.IIb.WindowHeatEq) (h3 : UnforcedLeray.Short.IIb.CylHeatMaxReg) (h4 : UnforcedLeray.Short.IIb.CylGradInterp) (h5 : UnforcedLeray.Short.IIb.WindowWeightCompare) : UnforcedLeray.Short.IIb.WindowBound :=
  windowBound_of_scalar (wbdScalar_of h1 h2 h3 h4 h5 wbdData wbdTransfer wbdNorms)

end UnforcedLeray.Short.IIb
