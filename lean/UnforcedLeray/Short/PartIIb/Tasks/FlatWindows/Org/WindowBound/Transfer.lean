import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_7_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiMollify.MollLoc
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.WindowBound.Transfer.WbdIntH

/-!
# `PartII-b:T13/1/7/2` assembly: transfer of the weak identities to the window

Source: `the November 2 reference manuscript` lines 1928-1933.  The target is the
composition `wbdTransfer_of` (proved in `Sub/PartII-b_T13_1_7_2.lean`) applied to the two leaves
`mollLoc_proof` (local integrability of periodic `L^r(cylMeas)` functions) and `wbdIntH_proof`
(integrability of `b ∈ H_r` against tests in `s > 0`).
-/

set_option autoImplicit false

theorem wbdTransfer : UnforcedLeray.Short.IIb.WbdTransfer :=
  UnforcedLeray.Short.IIb.wbdTransfer_of UnforcedLeray.Short.IIb.mollLoc_proof
    UnforcedLeray.Short.IIb.wbdIntH_proof
