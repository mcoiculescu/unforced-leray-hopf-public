import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_6_2
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiLimitWeak.localL1
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylGradInterp.cgiLimitWeak.ibp

/-!
# Weak identity for the cylinder limit (`CgiLimitWeak`, task `PartII-b:T13/1/5/6/2`)

Source of record: `the November 2 reference manuscript` lines 1933-1934.
The proof is `cgiLimitWeak_of` (Sub file) applied to the two leaf proofs `cgiLocalL1_proof`
(local `L¹` bound) and `cgiIBP_proof` (integration by parts).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem cgiLimitWeak_proof : UnforcedLeray.Short.IIb.CgiLimitWeak :=
  cgiLimitWeak_of cgiLocalL1_proof cgiIBP_proof

end UnforcedLeray.Short.IIb
