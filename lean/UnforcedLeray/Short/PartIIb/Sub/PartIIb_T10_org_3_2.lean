import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_of
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_1
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_3_2_2

/-!
# `PartII-b:T10/org/3/2`: `AdjointLerayCommute`

Source `the November 2 reference manuscript`,
lines 1359-1361, 1474-1475, 1498-1500. The statement is assembled from the two accepted siblings:
`lerayTestSchwartz` (`PartII-b:T10/org/3/2/1`) and `lerayTestComm` (`PartII-b:T10/org/3/2/2`),
via the decomposition lemma `adjointLerayCommute_of` (`PartII-b:T10/org/3/2`, `_of` file).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem adjointLerayCommute : UnforcedLeray.Short.IIb.AdjointLerayCommute :=
  adjointLerayCommute_of lerayTestSchwartz lerayTestComm

end UnforcedLeray.Short.IIb
